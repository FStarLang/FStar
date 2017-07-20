open Prims
let subst_to_string :
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____22 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____40  ->
              match uu____40 with
              | (b,uu____46) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____22 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____57 'Auu____58 .
    ('Auu____58 -> 'Auu____57 FStar_Pervasives_Native.option) ->
      'Auu____58 Prims.list ->
        ('Auu____58 Prims.list,'Auu____57) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____98 = f s0  in
          (match uu____98 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____130 'Auu____131 'Auu____132 .
    ('Auu____132 -> 'Auu____131 -> 'Auu____130) ->
      'Auu____130 ->
        ('Auu____132,'Auu____131) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____130
  =
  fun f  ->
    fun x  ->
      fun uu___103_156  ->
        match uu___103_156 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____191 'Auu____192 'Auu____193 .
    ('Auu____193 -> 'Auu____192 FStar_Pervasives_Native.option) ->
      'Auu____193 Prims.list ->
        ('Auu____193 Prims.list -> 'Auu____192 -> 'Auu____191) ->
          'Auu____191 -> 'Auu____191
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____237 = apply_until_some f s  in
          FStar_All.pipe_right uu____237 (map_some_curry g t)
  
let compose_subst :
  'Auu____264 'Auu____265 .
    ('Auu____265 Prims.list,'Auu____264 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____265 Prims.list,'Auu____264 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____265 Prims.list,'Auu____264 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Pervasives_Native.Some uu____334 ->
            FStar_Pervasives_Native.snd s2
        | uu____339 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____447 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,uu____473) ->
        let uu____498 = FStar_Syntax_Unionfind.find uv  in
        (match uu____498 with
         | FStar_Pervasives_Native.Some t' -> force_uvar' t'
         | uu____504 -> t)
    | uu____507 -> t
  
let force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    let t' = force_uvar' t  in
    let uu____521 = FStar_Util.physical_equality t t'  in
    if uu____521
    then t
    else
      delay t'
        ([], (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)))
  
let rec force_delayed_thunk :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____589 = FStar_ST.read m  in
        (match uu____589 with
         | FStar_Pervasives_Native.None  -> t
         | FStar_Pervasives_Native.Some t' ->
             let t'1 = force_delayed_thunk t'  in
             (FStar_ST.write m (FStar_Pervasives_Native.Some t'1); t'1))
    | uu____621 -> t
  
let rec compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____635 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____635 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____639 -> u)
    | uu____642 -> u
  
let subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___104_661  ->
           match uu___104_661 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____666 =
                 let uu____667 =
                   let uu____668 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____668  in
                 FStar_Syntax_Syntax.bv_to_name uu____667  in
               FStar_Pervasives_Native.Some uu____666
           | uu____669 -> FStar_Pervasives_Native.None)
  
let subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___105_688  ->
           match uu___105_688 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____693 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___109_696 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___109_696.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___109_696.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____693
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____705 -> FStar_Pervasives_Native.None)
  
let subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___106_723  ->
           match uu___106_723 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____728 -> FStar_Pervasives_Native.None)
  
let subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___107_746  ->
           match uu___107_746 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____751 -> FStar_Pervasives_Native.None)
  
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
      | FStar_Syntax_Syntax.U_unif uu____775 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____785 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____785
      | FStar_Syntax_Syntax.U_max us ->
          let uu____789 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____789
  
let tag_with_range :
  'Auu____798 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____798,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> t
      | FStar_Pervasives_Native.Some r ->
          let r1 = FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r  in
          let t' =
            match t.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_bvar bv ->
                let uu____831 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                FStar_Syntax_Syntax.Tm_bvar uu____831
            | FStar_Syntax_Syntax.Tm_name bv ->
                let uu____833 = FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                FStar_Syntax_Syntax.Tm_name uu____833
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                let v1 =
                  let uu___110_839 = fv.FStar_Syntax_Syntax.fv_name  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r1);
                    FStar_Syntax_Syntax.p =
                      (uu___110_839.FStar_Syntax_Syntax.p)
                  }  in
                let fv1 =
                  let uu___111_841 = fv  in
                  {
                    FStar_Syntax_Syntax.fv_name = v1;
                    FStar_Syntax_Syntax.fv_delta =
                      (uu___111_841.FStar_Syntax_Syntax.fv_delta);
                    FStar_Syntax_Syntax.fv_qual =
                      (uu___111_841.FStar_Syntax_Syntax.fv_qual)
                  }  in
                FStar_Syntax_Syntax.Tm_fvar fv1
            | t' -> t'  in
          let uu___112_843 = t  in
          {
            FStar_Syntax_Syntax.n = t';
            FStar_Syntax_Syntax.pos = r1;
            FStar_Syntax_Syntax.vars =
              (uu___112_843.FStar_Syntax_Syntax.vars)
          }
  
let tag_lid_with_range :
  'Auu____852 .
    FStar_Ident.lident ->
      ('Auu____852,FStar_Range.range FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> l
      | FStar_Pervasives_Native.Some r ->
          let uu____876 =
            FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r  in
          FStar_Ident.set_lid_range l uu____876
  
let mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Pervasives_Native.None  -> r
      | FStar_Pervasives_Native.Some r' -> FStar_Range.set_use_range r r'
  
let rec subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____994 ->
          let t0 = force_delayed_thunk t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1004 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1009 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_uvar uu____1014 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1123 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1124 =
                 let uu____1127 =
                   let uu____1128 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1128  in
                 FStar_Syntax_Syntax.mk uu____1127  in
               uu____1124 FStar_Pervasives_Native.None uu____1123
           | uu____1138 ->
               let uu____1139 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1139)

and subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___108_1153  ->
              match uu___108_1153 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1157 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1157
              | f -> f))

and subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1191 ->
          let uu___113_1202 = t  in
          let uu____1203 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1210 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1215 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1218 =
            FStar_List.map
              (fun uu____1243  ->
                 match uu____1243 with
                 | (t1,imp) ->
                     let uu____1262 = subst' s t1  in (uu____1262, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1267 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1203;
            FStar_Syntax_Syntax.effect_name = uu____1210;
            FStar_Syntax_Syntax.result_typ = uu____1215;
            FStar_Syntax_Syntax.effect_args = uu____1218;
            FStar_Syntax_Syntax.flags = uu____1267
          }

and subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Range.range
                                                         FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Pervasives_Native.None ) -> t
      | ([]::[],FStar_Pervasives_Native.None ) -> t
      | uu____1304 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1327 = subst' s t1  in
               let uu____1328 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1327 uu____1328
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1347 = subst' s t1  in
               let uu____1348 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1347 uu____1348
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1358 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1358)

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
      | FStar_Syntax_Syntax.NT uu____1375 -> s
  
let shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1396 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1396)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1396)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1423 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1423, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1442 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1442) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1442) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1458  ->
      match uu____1458 with
      | (x,imp) ->
          let uu____1465 =
            let uu___114_1466 = x  in
            let uu____1467 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___114_1466.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___114_1466.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1467
            }  in
          (uu____1465, imp)
  
let subst_binders' :
  'Auu____1476 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1476) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1476) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1536 = shift_subst' i s  in
                   subst_binder' uu____1536 b)))
  
let subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  -> fun bs  -> subst_binders' ([s], FStar_Pervasives_Native.None) bs 
let subst_arg' :
  'Auu____1567 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1567)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1567)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1587  ->
      match uu____1587 with
      | (t,imp) -> let uu____1600 = subst' s t  in (uu____1600, imp)
  
let subst_args' :
  'Auu____1610 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1610)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1610)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Range.range
                                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1700 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1721 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1775  ->
                      fun uu____1776  ->
                        match (uu____1775, uu____1776) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1855 = aux n2 p2  in
                            (match uu____1855 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1721 with
             | (pats1,n2) ->
                 ((let uu___115_1913 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___115_1913.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___116_1939 = x  in
              let uu____1940 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___116_1939.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___116_1939.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1940
              }  in
            ((let uu___117_1946 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___117_1946.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___118_1962 = x  in
              let uu____1963 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___118_1962.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___118_1962.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1963
              }  in
            ((let uu___119_1969 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___119_1969.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___120_1990 = x  in
              let uu____1991 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___120_1990.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___120_1990.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1991
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___121_2000 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___121_2000.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2022 =
            let uu___122_2023 = rc  in
            let uu____2024 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___122_2023.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2024;
              FStar_Syntax_Syntax.residual_flags =
                (uu___122_2023.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2022
  
let push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2053 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2053  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2056 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_constant uu____2083 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2088 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar uu____2097 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_type uu____2118 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2119 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2120 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2136 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2136 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2165 =
            let uu____2166 =
              let uu____2181 = subst' s t0  in
              let uu____2184 = subst_args' s args  in
              (uu____2181, uu____2184)  in
            FStar_Syntax_Syntax.Tm_app uu____2166  in
          mk1 uu____2165
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2279 = subst' s t1  in FStar_Util.Inl uu____2279
            | FStar_Util.Inr c ->
                let uu____2293 = subst_comp' s c  in
                FStar_Util.Inr uu____2293
             in
          let uu____2300 =
            let uu____2301 =
              let uu____2328 = subst' s t0  in
              let uu____2331 =
                let uu____2348 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2348)  in
              (uu____2328, uu____2331, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2301  in
          mk1 uu____2300
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2432 =
            let uu____2433 =
              let uu____2450 = subst_binders' s bs  in
              let uu____2457 = subst' s' body  in
              let uu____2460 = push_subst_lcomp s' lopt  in
              (uu____2450, uu____2457, uu____2460)  in
            FStar_Syntax_Syntax.Tm_abs uu____2433  in
          mk1 uu____2432
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2496 =
            let uu____2497 =
              let uu____2510 = subst_binders' s bs  in
              let uu____2517 =
                let uu____2520 = shift_subst' n1 s  in
                subst_comp' uu____2520 comp  in
              (uu____2510, uu____2517)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2497  in
          mk1 uu____2496
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___123_2552 = x  in
            let uu____2553 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_2552.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_2552.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2553
            }  in
          let phi1 =
            let uu____2559 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____2559 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2686  ->
                    match uu____2686 with
                    | (pat,wopt,branch) ->
                        let uu____2732 = subst_pat' s pat  in
                        (match uu____2732 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____2780 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____2780
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
                      let uu____2865 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____2865
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___124_2880 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_2880.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_2880.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___125_2882 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_2882.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_2882.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____2909 =
            let uu____2910 =
              let uu____2917 = subst' s t0  in
              let uu____2920 =
                let uu____2921 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____2921  in
              (uu____2917, uu____2920)  in
            FStar_Syntax_Syntax.Tm_meta uu____2910  in
          mk1 uu____2909
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____2981 =
            let uu____2982 =
              let uu____2989 = subst' s t0  in
              let uu____2992 =
                let uu____2993 =
                  let uu____3000 = subst' s t1  in (m, uu____3000)  in
                FStar_Syntax_Syntax.Meta_monadic uu____2993  in
              (uu____2989, uu____2992)  in
            FStar_Syntax_Syntax.Tm_meta uu____2982  in
          mk1 uu____2981
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3019 =
            let uu____3020 =
              let uu____3027 = subst' s t0  in
              let uu____3030 =
                let uu____3031 =
                  let uu____3040 = subst' s t1  in (m1, m2, uu____3040)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3031  in
              (uu____3027, uu____3030)  in
            FStar_Syntax_Syntax.Tm_meta uu____3020  in
          mk1 uu____3019
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3053 =
            let uu____3054 = let uu____3061 = subst' s t1  in (uu____3061, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3054  in
          mk1 uu____3053
  
let rec compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = force_delayed_thunk t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed ((t2,s),memo) ->
        let t' = let uu____3125 = push_subst s t2  in compress uu____3125  in
        (FStar_Syntax_Unionfind.update_in_tx memo
           (FStar_Pervasives_Native.Some t');
         t')
    | uu____3133 ->
        let t' = force_uvar t1  in
        (match t'.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed uu____3137 -> compress t'
         | uu____3162 -> t')
  
let subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun t  -> subst' ([s], FStar_Pervasives_Native.None) t 
let set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun r  ->
    fun t  ->
      subst'
        ([],
          (FStar_Pervasives_Native.Some
             (let uu___126_3202 = r  in
              {
                FStar_Range.def_range = (r.FStar_Range.use_range);
                FStar_Range.use_range = (uu___126_3202.FStar_Range.use_range)
              }))) t
  
let subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Pervasives_Native.None) t 
let closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun bs  ->
    let uu____3231 =
      FStar_List.fold_right
        (fun uu____3254  ->
           fun uu____3255  ->
             match (uu____3254, uu____3255) with
             | ((x,uu____3283),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3231 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3318 .
    (FStar_Syntax_Syntax.bv,'Auu____3318) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3318) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___127_3424 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3425 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_3424.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_3424.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3425
            }  in
          let o1 =
            let uu____3431 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3431
             in
          let uu____3434 = aux bs' o1  in
          (match uu____3434 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let open_binders : FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun bs  ->
    let uu____3493 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3493
  
let open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3
  =
  fun bs  ->
    fun t  ->
      let uu____3528 = open_binders' bs  in
      match uu____3528 with
      | (bs',opening) ->
          let uu____3565 = subst opening t  in (bs', uu____3565, opening)
  
let open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3586 = open_term' bs t  in
      match uu____3586 with | (b,t1,uu____3599) -> (b, t1)
  
let open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      let uu____3612 = open_binders' bs  in
      match uu____3612 with
      | (bs',opening) ->
          let uu____3647 = subst_comp opening t  in (bs', uu____3647)
  
let open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec open_pat_aux sub1 renaming p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3728 -> (p1, sub1, renaming)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3757 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____3849  ->
                    fun uu____3850  ->
                      match (uu____3849, uu____3850) with
                      | ((pats1,sub2,renaming1),(p2,imp)) ->
                          let uu____3998 = open_pat_aux sub2 renaming1 p2  in
                          (match uu____3998 with
                           | (p3,sub3,renaming2) ->
                               (((p3, imp) :: pats1), sub3, renaming2)))
                 ([], sub1, renaming))
             in
          (match uu____3757 with
           | (pats1,sub2,renaming1) ->
               ((let uu___128_4168 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___128_4168.FStar_Syntax_Syntax.p)
                 }), sub2, renaming1))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___129_4187 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4188 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_4187.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_4187.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4188
            }  in
          let sub2 =
            let uu____4194 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4194
             in
          ((let uu___130_4208 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___130_4208.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___131_4217 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4218 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_4217.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_4217.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4218
            }  in
          let sub2 =
            let uu____4224 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4224
             in
          ((let uu___132_4238 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___132_4238.FStar_Syntax_Syntax.p)
            }), sub2, ((x, x') :: renaming))
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___133_4252 = x  in
            let uu____4253 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_4252.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_4252.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4253
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___134_4268 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___134_4268.FStar_Syntax_Syntax.p)
            }), sub1, renaming)
       in
    let uu____4271 = open_pat_aux [] [] p  in
    match uu____4271 with | (p1,sub1,uu____4298) -> (p1, sub1)
  
let open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4326  ->
    match uu____4326 with
    | (p,wopt,e) ->
        let uu____4346 = open_pat p  in
        (match uu____4346 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4365 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4365
                in
             let e1 = subst opening e  in (p1, wopt1, e1))
  
let close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> let uu____4377 = closing_subst bs  in subst uu____4377 t
  
let close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun bs  ->
    fun c  -> let uu____4388 = closing_subst bs  in subst_comp uu____4388 c
  
let close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___135_4440 = x  in
            let uu____4441 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_4440.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_4440.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4441
            }  in
          let s' =
            let uu____4447 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4447
             in
          let uu____4450 = aux s' tl1  in (x1, imp) :: uu____4450
       in
    aux [] bs
  
let close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      let uu___136_4472 = lc  in
      let uu____4473 = subst s lc.FStar_Syntax_Syntax.res_typ  in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___136_4472.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = uu____4473;
        FStar_Syntax_Syntax.cflags =
          (uu___136_4472.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____4478  ->
             let uu____4479 = lc.FStar_Syntax_Syntax.comp ()  in
             subst_comp s uu____4479)
      }
  
let close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4527 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4550 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4616  ->
                    fun uu____4617  ->
                      match (uu____4616, uu____4617) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4720 = aux sub2 p2  in
                          (match uu____4720 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4550 with
           | (pats1,sub2) ->
               ((let uu___137_4822 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___137_4822.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___138_4841 = x  in
            let uu____4842 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_4841.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_4841.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4842
            }  in
          let sub2 =
            let uu____4848 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4848
             in
          ((let uu___139_4856 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___139_4856.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___140_4861 = x  in
            let uu____4862 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_4861.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_4861.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4862
            }  in
          let sub2 =
            let uu____4868 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4868
             in
          ((let uu___141_4876 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___141_4876.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___142_4886 = x  in
            let uu____4887 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___142_4886.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___142_4886.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4887
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___143_4896 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___143_4896.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun uu____4902  ->
    match uu____4902 with
    | (p,wopt,e) ->
        let uu____4922 = close_pat p  in
        (match uu____4922 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4953 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____4953
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun t  ->
      let uu____5012 = univ_var_opening us  in
      match uu____5012 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2
  =
  fun us  ->
    fun c  ->
      let uu____5054 = univ_var_opening us  in
      match uu____5054 with
      | (s,us') -> let uu____5077 = subst_comp s c  in (us', uu____5077)
  
let close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
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
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5127 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____5127
      then (lbs, t)
      else
        (let uu____5137 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____5165  ->
                  match uu____5165 with
                  | (i,lbs1,out) ->
                      let x =
                        let uu____5198 =
                          FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                        FStar_Syntax_Syntax.freshen_bv uu____5198  in
                      ((i + (Prims.parse_int "1")),
                        ((let uu___144_5204 = lb  in
                          {
                            FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                            FStar_Syntax_Syntax.lbunivs =
                              (uu___144_5204.FStar_Syntax_Syntax.lbunivs);
                            FStar_Syntax_Syntax.lbtyp =
                              (uu___144_5204.FStar_Syntax_Syntax.lbtyp);
                            FStar_Syntax_Syntax.lbeff =
                              (uu___144_5204.FStar_Syntax_Syntax.lbeff);
                            FStar_Syntax_Syntax.lbdef =
                              (uu___144_5204.FStar_Syntax_Syntax.lbdef)
                          }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                        out))) lbs ((Prims.parse_int "0"), [], [])
            in
         match uu____5137 with
         | (n_let_recs,lbs1,let_rec_opening) ->
             let lbs2 =
               FStar_All.pipe_right lbs1
                 (FStar_List.map
                    (fun lb  ->
                       let uu____5241 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____5268  ->
                                match uu____5268 with
                                | (i,us,out) ->
                                    ((i + (Prims.parse_int "1")), (u :: us),
                                      ((FStar_Syntax_Syntax.UN
                                          (i, (FStar_Syntax_Syntax.U_name u)))
                                      :: out)))
                           lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, [], let_rec_opening)
                          in
                       match uu____5241 with
                       | (uu____5308,us,u_let_rec_opening) ->
                           let uu___145_5319 = lb  in
                           let uu____5320 =
                             subst u_let_rec_opening
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___145_5319.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs = us;
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___145_5319.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___145_5319.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5320
                           }))
                in
             let t1 = subst let_rec_opening t  in (lbs2, t1))
  
let close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun lbs  ->
    fun t  ->
      let uu____5344 = FStar_Syntax_Syntax.is_top_level lbs  in
      if uu____5344
      then (lbs, t)
      else
        (let uu____5354 =
           FStar_List.fold_right
             (fun lb  ->
                fun uu____5373  ->
                  match uu____5373 with
                  | (i,out) ->
                      let uu____5392 =
                        let uu____5395 =
                          let uu____5396 =
                            let uu____5401 =
                              FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                               in
                            (uu____5401, i)  in
                          FStar_Syntax_Syntax.NM uu____5396  in
                        uu____5395 :: out  in
                      ((i + (Prims.parse_int "1")), uu____5392)) lbs
             ((Prims.parse_int "0"), [])
            in
         match uu____5354 with
         | (n_let_recs,let_rec_closing) ->
             let lbs1 =
               FStar_All.pipe_right lbs
                 (FStar_List.map
                    (fun lb  ->
                       let uu____5432 =
                         FStar_List.fold_right
                           (fun u  ->
                              fun uu____5450  ->
                                match uu____5450 with
                                | (i,out) ->
                                    ((i + (Prims.parse_int "1")),
                                      ((FStar_Syntax_Syntax.UD (u, i)) ::
                                      out))) lb.FStar_Syntax_Syntax.lbunivs
                           (n_let_recs, let_rec_closing)
                          in
                       match uu____5432 with
                       | (uu____5473,u_let_rec_closing) ->
                           let uu___146_5479 = lb  in
                           let uu____5480 =
                             subst u_let_rec_closing
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___146_5479.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___146_5479.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___146_5479.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___146_5479.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____5480
                           }))
                in
             let t1 = subst let_rec_closing t  in (lbs1, t1))
  
let close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun binders  ->
    fun uu____5493  ->
      match uu____5493 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5518  ->
                   match uu____5518 with
                   | (x,uu____5524) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme
  =
  fun us  ->
    fun uu____5541  ->
      match uu____5541 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5563 = subst s t  in (us', uu____5563)
  
let opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5586  ->
              match uu____5586 with
              | (x,uu____5592) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t =
  fun bs  -> closing_subst bs 