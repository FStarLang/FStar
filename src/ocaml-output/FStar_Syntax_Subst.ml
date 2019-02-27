open Prims
let subst_to_string :
  'Auu____42271 .
    (FStar_Syntax_Syntax.bv * 'Auu____42271) Prims.list -> Prims.string
  =
  fun s  ->
    let uu____42290 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____42311  ->
              match uu____42311 with
              | (b,uu____42318) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____42290 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____42333 'Auu____42334 .
    ('Auu____42333 -> 'Auu____42334 FStar_Pervasives_Native.option) ->
      'Auu____42333 Prims.list ->
        ('Auu____42333 Prims.list * 'Auu____42334)
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____42376 = f s0  in
          (match uu____42376 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____42409 'Auu____42410 'Auu____42411 .
    ('Auu____42409 -> 'Auu____42410 -> 'Auu____42411) ->
      'Auu____42411 ->
        ('Auu____42409 * 'Auu____42410) FStar_Pervasives_Native.option ->
          'Auu____42411
  =
  fun f  ->
    fun x  ->
      fun uu___391_42438  ->
        match uu___391_42438 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____42474 'Auu____42475 'Auu____42476 .
    ('Auu____42474 -> 'Auu____42475 FStar_Pervasives_Native.option) ->
      'Auu____42474 Prims.list ->
        ('Auu____42474 Prims.list -> 'Auu____42475 -> 'Auu____42476) ->
          'Auu____42476 -> 'Auu____42476
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____42524 = apply_until_some f s  in
          FStar_All.pipe_right uu____42524 (map_some_curry g t)
  
let compose_subst :
  'Auu____42550 .
    ('Auu____42550 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
      ('Auu____42550 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range) ->
        ('Auu____42550 Prims.list * FStar_Syntax_Syntax.maybe_set_use_range)
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____42601 ->
            FStar_Pervasives_Native.snd s2
        | uu____42604 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range) -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____42687 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____42713;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____42714;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____42715;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____42716;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____42717;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____42718;
           FStar_Syntax_Syntax.ctx_uvar_meta = uu____42719;_},s)
        ->
        let uu____42768 = FStar_Syntax_Unionfind.find uv  in
        (match uu____42768 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____42779 =
               let uu____42782 =
                 let uu____42790 = delay t' s  in force_uvar' uu____42790  in
               FStar_Pervasives_Native.fst uu____42782  in
             (uu____42779, true)
         | uu____42800 -> (t, false))
    | uu____42807 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    let uu____42829 = force_uvar' t  in
    match uu____42829 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____42865 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____42865, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * Prims.bool))
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____42939 = FStar_ST.op_Bang m  in
        (match uu____42939 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____43011 = try_read_memo_aux t'  in
             (match uu____43011 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____43093 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43110 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____43110
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____43136 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____43136 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____43140 -> u)
    | uu____43143 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___392_43165  ->
           match uu___392_43165 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____43173 =
                 let uu____43174 =
                   let uu____43175 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____43175  in
                 FStar_Syntax_Syntax.bv_to_name uu____43174  in
               FStar_Pervasives_Native.Some uu____43173
           | uu____43176 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___393_43202  ->
           match uu___393_43202 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____43211 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___499_43216 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___499_43216.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___499_43216.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____43211
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____43227 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___394_43252  ->
           match uu___394_43252 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____43260 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___395_43281  ->
           match uu___395_43281 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____43289 -> FStar_Pervasives_Native.None)
  
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
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
      | FStar_Syntax_Syntax.U_unif uu____43317 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____43327 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____43327
      | FStar_Syntax_Syntax.U_max us ->
          let uu____43331 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____43331
  
let tag_with_range :
  'Auu____43341 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____43341 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43367 =
            let uu____43369 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____43370 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43369 uu____43370  in
          if uu____43367
          then t
          else
            (let r1 =
               let uu____43377 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos
                 uu____43377
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____43380 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_bvar uu____43380
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____43382 =
                     FStar_Syntax_Syntax.set_range_of_bv bv r1  in
                   FStar_Syntax_Syntax.Tm_name uu____43382
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___551_43388 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____43389 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____43389;
                       FStar_Syntax_Syntax.p =
                         (uu___551_43388.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___554_43391 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___554_43391.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___554_43391.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___559_43393 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___559_43393.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____43403 .
    FStar_Ident.lident ->
      ('Auu____43403 * FStar_Syntax_Syntax.maybe_set_use_range) ->
        FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____43423 =
            let uu____43425 =
              let uu____43426 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____43426  in
            let uu____43427 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____43425 uu____43427  in
          if uu____43423
          then l
          else
            (let uu____43431 =
               let uu____43432 = FStar_Ident.range_of_lid l  in
               let uu____43433 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____43432 uu____43433  in
             FStar_Ident.set_lid_range l uu____43431)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____43450 =
            let uu____43452 = FStar_Range.use_range r  in
            let uu____43453 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____43452 uu____43453  in
          if uu____43450
          then r
          else
            (let uu____43457 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____43457)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____43578 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____43586 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____43591 -> tag_with_range t0 s
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
               let uu____43660 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____43661 =
                 let uu____43668 =
                   let uu____43669 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____43669  in
                 FStar_Syntax_Syntax.mk uu____43668  in
               uu____43661 FStar_Pervasives_Native.None uu____43660
           | uu____43677 ->
               let uu____43678 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____43678)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___396_43690  ->
              match uu___396_43690 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____43694 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____43694
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____43722 ->
          let uu___620_43731 = t  in
          let uu____43732 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____43737 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____43742 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____43745 =
            FStar_List.map
              (fun uu____43773  ->
                 match uu____43773 with
                 | (t1,imp) ->
                     let uu____43792 = subst' s t1  in
                     let uu____43793 = subst_imp' s imp  in
                     (uu____43792, uu____43793))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____43798 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____43732;
            FStar_Syntax_Syntax.effect_name = uu____43737;
            FStar_Syntax_Syntax.result_typ = uu____43742;
            FStar_Syntax_Syntax.effect_args = uu____43745;
            FStar_Syntax_Syntax.flags = uu____43798
          }

and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____43829 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____43850 = subst' s t1  in
               let uu____43851 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____43850 uu____43851
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____43868 = subst' s t1  in
               let uu____43869 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____43868 uu____43869
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____43877 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____43877)

and (subst_imp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun i  ->
      match i with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____43895 =
            let uu____43896 = subst' s t  in
            FStar_Syntax_Syntax.Meta uu____43896  in
          FStar_Pervasives_Native.Some uu____43895
      | i1 -> i1

let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____43935 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____43962 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43962) ->
        (FStar_Syntax_Syntax.subst_t Prims.list * 'Auu____43962)
  =
  fun n1  ->
    fun s  ->
      let uu____43993 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____43993, (FStar_Pervasives_Native.snd s))
  
let (subst_binder' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option))
  =
  fun s  ->
    fun uu____44036  ->
      match uu____44036 with
      | (x,imp) ->
          let uu____44063 =
            let uu___679_44064 = x  in
            let uu____44065 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___679_44064.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___679_44064.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____44065
            }  in
          let uu____44068 = subst_imp' s imp  in (uu____44063, uu____44068)
  
let (subst_binders' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
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
                  (let uu____44174 = shift_subst' i s  in
                   subst_binder' uu____44174 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____44213 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44213) ->
        (FStar_Syntax_Syntax.term * 'Auu____44213)
  =
  fun s  ->
    fun uu____44231  ->
      match uu____44231 with
      | (t,imp) -> let uu____44238 = subst' s t  in (uu____44238, imp)
  
let subst_args' :
  'Auu____44245 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term * 'Auu____44245) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____44245) Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list *
    FStar_Syntax_Syntax.maybe_set_use_range) ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat * Prims.int))
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____44339 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____44361 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____44423  ->
                      fun uu____44424  ->
                        match (uu____44423, uu____44424) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____44520 = aux n2 p2  in
                            (match uu____44520 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____44361 with
             | (pats1,n2) ->
                 ((let uu___716_44594 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___716_44594.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___721_44620 = x  in
              let uu____44621 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___721_44620.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___721_44620.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44621
              }  in
            ((let uu___724_44626 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p =
                  (uu___724_44626.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___729_44639 = x  in
              let uu____44640 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___729_44639.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___729_44639.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44640
              }  in
            ((let uu___732_44645 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p =
                  (uu___732_44645.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___739_44663 = x  in
              let uu____44664 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___739_44663.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___739_44663.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____44664
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___743_44670 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p =
                  (uu___743_44670.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____44696 =
            let uu___750_44697 = rc  in
            let uu____44698 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___750_44697.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____44698;
              FStar_Syntax_Syntax.residual_flags =
                (uu___750_44697.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____44696
  
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_ts ->
      FStar_Syntax_Syntax.subst_ts -> FStar_Syntax_Syntax.subst_ts)
  =
  fun u  ->
    fun s0  ->
      fun s  ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun uu____44748  ->
                  match uu____44748 with
                  | (x',uu____44757) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___398_44773 =
          match uu___398_44773 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___397_44804  ->
                        match uu___397_44804 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____44813 = should_retain x  in
                            if uu____44813
                            then
                              let uu____44818 =
                                let uu____44819 =
                                  let uu____44826 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____44826)  in
                                FStar_Syntax_Syntax.NT uu____44819  in
                              [uu____44818]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____44841 = should_retain x  in
                            if uu____44841
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___777_44849 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___777_44849.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___777_44849.FStar_Syntax_Syntax.sort)
                                   })
                                 in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i
                                 in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____44859 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____44864 -> []))
                 in
              let uu____44865 = aux rest  in
              FStar_List.append hd1 uu____44865
           in
        let uu____44868 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____44868 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____44931 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____44931
         in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____44934 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          (match i.FStar_Syntax_Syntax.lkind with
           | FStar_Syntax_Syntax.Lazy_embedding uu____44963 ->
               let t1 =
                 let uu____44973 =
                   let uu____44982 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____44982  in
                 uu____44973 i.FStar_Syntax_Syntax.lkind i  in
               push_subst s t1
           | uu____45032 -> t)
      | FStar_Syntax_Syntax.Tm_constant uu____45033 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____45038 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____45065 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____45065 with
           | FStar_Pervasives_Native.None  ->
               let uu____45070 =
                 let uu___810_45073 = t  in
                 let uu____45076 =
                   let uu____45077 =
                     let uu____45090 = compose_uvar_subst uv s0 s  in
                     (uv, uu____45090)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____45077  in
                 {
                   FStar_Syntax_Syntax.n = uu____45076;
                   FStar_Syntax_Syntax.pos =
                     (uu___810_45073.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___810_45073.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____45070 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____45114 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____45115 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____45116 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____45130 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____45130 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____45163 =
            let uu____45164 =
              let uu____45181 = subst' s t0  in
              let uu____45184 = subst_args' s args  in
              (uu____45181, uu____45184)  in
            FStar_Syntax_Syntax.Tm_app uu____45164  in
          mk1 uu____45163
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____45285 = subst' s t1  in FStar_Util.Inl uu____45285
            | FStar_Util.Inr c ->
                let uu____45299 = subst_comp' s c  in
                FStar_Util.Inr uu____45299
             in
          let uu____45306 =
            let uu____45307 =
              let uu____45334 = subst' s t0  in
              let uu____45337 =
                let uu____45354 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____45354)  in
              (uu____45334, uu____45337, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____45307  in
          mk1 uu____45306
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____45440 =
            let uu____45441 =
              let uu____45460 = subst_binders' s bs  in
              let uu____45469 = subst' s' body  in
              let uu____45472 = push_subst_lcomp s' lopt  in
              (uu____45460, uu____45469, uu____45472)  in
            FStar_Syntax_Syntax.Tm_abs uu____45441  in
          mk1 uu____45440
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____45516 =
            let uu____45517 =
              let uu____45532 = subst_binders' s bs  in
              let uu____45541 =
                let uu____45544 = shift_subst' n1 s  in
                subst_comp' uu____45544 comp  in
              (uu____45532, uu____45541)  in
            FStar_Syntax_Syntax.Tm_arrow uu____45517  in
          mk1 uu____45516
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___857_45574 = x  in
            let uu____45575 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___857_45574.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___857_45574.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____45575
            }  in
          let phi1 =
            let uu____45579 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____45579 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____45695  ->
                    match uu____45695 with
                    | (pat,wopt,branch) ->
                        let uu____45725 = subst_pat' s pat  in
                        (match uu____45725 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____45756 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____45756
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
                      let uu____45828 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____45828
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___895_45846 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___895_45846.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___895_45846.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___900_45848 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___900_45848.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___900_45848.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___900_45848.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___900_45848.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____45879 =
            let uu____45880 =
              let uu____45887 = subst' s t0  in
              let uu____45890 =
                let uu____45891 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____45891  in
              (uu____45887, uu____45890)  in
            FStar_Syntax_Syntax.Tm_meta uu____45880  in
          mk1 uu____45879
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____45957 =
            let uu____45958 =
              let uu____45965 = subst' s t0  in
              let uu____45968 =
                let uu____45969 =
                  let uu____45976 = subst' s t1  in (m, uu____45976)  in
                FStar_Syntax_Syntax.Meta_monadic uu____45969  in
              (uu____45965, uu____45968)  in
            FStar_Syntax_Syntax.Tm_meta uu____45958  in
          mk1 uu____45957
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____45995 =
            let uu____45996 =
              let uu____46003 = subst' s t0  in
              let uu____46006 =
                let uu____46007 =
                  let uu____46016 = subst' s t1  in (m1, m2, uu____46016)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____46007  in
              (uu____46003, uu____46006)  in
            FStar_Syntax_Syntax.Tm_meta uu____45996  in
          mk1 uu____45995
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____46031 =
                 let uu____46032 =
                   let uu____46039 = subst' s tm  in (uu____46039, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____46032  in
               mk1 uu____46031
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____46053 =
            let uu____46054 =
              let uu____46061 = subst' s t1  in (uu____46061, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____46054  in
          mk1 uu____46053
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____46075 = force_uvar t1  in
    match uu____46075 with
    | (t2,uu____46084) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____46137 =
                 let uu____46142 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____46142  in
               FStar_ST.op_Colon_Equals memo uu____46137);
              compress t2)
         | uu____46196 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____46231 =
        let uu____46232 =
          let uu____46233 =
            let uu____46234 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____46234  in
          FStar_Syntax_Syntax.SomeUseRange uu____46233  in
        ([], uu____46232)  in
      subst' uu____46231 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (subst_imp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual)
  =
  fun s  -> fun imp  -> subst_imp' ([s], FStar_Syntax_Syntax.NoUseRange) imp 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____46295 =
      FStar_List.fold_right
        (fun uu____46322  ->
           fun uu____46323  ->
             match (uu____46322, uu____46323) with
             | ((x,uu____46358),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____46295 FStar_Pervasives_Native.fst
  
let (open_binders' :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___972_46516 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____46517 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___972_46516.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___972_46516.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____46517
            }  in
          let imp1 = subst_imp o imp  in
          let o1 =
            let uu____46524 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____46524
             in
          let uu____46530 = aux bs' o1  in
          (match uu____46530 with | (bs'1,o2) -> (((x', imp1) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____46591 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____46591
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.subst_t))
  =
  fun bs  ->
    fun t  ->
      let uu____46629 = open_binders' bs  in
      match uu____46629 with
      | (bs',opening) ->
          let uu____46666 = subst opening t  in (bs', uu____46666, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let uu____46682 = open_term' bs t  in
      match uu____46682 with | (b,t1,uu____46695) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun bs  ->
    fun t  ->
      let uu____46711 = open_binders' bs  in
      match uu____46711 with
      | (bs',opening) ->
          let uu____46746 = subst_comp opening t  in (bs', uu____46746)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____46796 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____46821 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____46892  ->
                    fun uu____46893  ->
                      match (uu____46892, uu____46893) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47007 = open_pat_aux sub2 p2  in
                          (match uu____47007 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____46821 with
           | (pats1,sub2) ->
               ((let uu___1019_47117 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1019_47117.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___1023_47138 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47139 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1023_47138.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1023_47138.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47139
            }  in
          let sub2 =
            let uu____47145 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47145
             in
          ((let uu___1027_47156 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___1027_47156.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___1031_47161 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____47162 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1031_47161.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1031_47161.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47162
            }  in
          let sub2 =
            let uu____47168 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____47168
             in
          ((let uu___1035_47179 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___1035_47179.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1041_47189 = x  in
            let uu____47190 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1041_47189.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1041_47189.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47190
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1045_47199 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1045_47199.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch * FStar_Syntax_Syntax.subst_t))
  =
  fun uu____47213  ->
    match uu____47213 with
    | (p,wopt,e) ->
        let uu____47237 = open_pat p  in
        (match uu____47237 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47266 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____47266
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____47286 = open_branch' br  in
    match uu____47286 with | (br1,uu____47292) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____47304 = closing_subst bs  in subst uu____47304 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____47318 = closing_subst bs  in subst_comp uu____47318 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___1077_47386 = x  in
            let uu____47387 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1077_47386.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1077_47386.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47387
            }  in
          let imp1 = subst_imp s imp  in
          let s' =
            let uu____47394 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47394
             in
          let uu____47400 = aux s' tl1  in (x1, imp1) :: uu____47400
       in
    aux [] bs
  
let (close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____47427  ->
           let uu____47428 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____47428)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____47482 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____47507 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____47578  ->
                    fun uu____47579  ->
                      match (uu____47578, uu____47579) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____47693 = aux sub2 p2  in
                          (match uu____47693 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____47507 with
           | (pats1,sub2) ->
               ((let uu___1108_47803 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___1108_47803.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___1112_47824 = x  in
            let uu____47825 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1112_47824.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1112_47824.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47825
            }  in
          let sub2 =
            let uu____47831 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47831
             in
          ((let uu___1116_47842 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___1116_47842.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___1120_47847 = x  in
            let uu____47848 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1120_47847.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1120_47847.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47848
            }  in
          let sub2 =
            let uu____47854 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____47854
             in
          ((let uu___1124_47865 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___1124_47865.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___1130_47875 = x  in
            let uu____47876 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1130_47875.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1130_47875.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____47876
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___1134_47885 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___1134_47885.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____47895  ->
    match uu____47895 with
    | (p,wopt,e) ->
        let uu____47915 = close_pat p  in
        (match uu____47915 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____47952 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____47952
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name
      Prims.list))
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
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term))
  =
  fun us  ->
    fun t  ->
      let uu____48040 = univ_var_opening us  in
      match uu____48040 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp))
  =
  fun us  ->
    fun c  ->
      let uu____48083 = univ_var_opening us  in
      match uu____48083 with
      | (s,us') -> let uu____48106 = subst_comp s c  in (us', uu____48106)
  
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
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
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____48169 =
        let uu____48181 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48181
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48221  ->
                 match uu____48221 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____48258 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____48258  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___1186_48266 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1186_48266.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___1186_48266.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1186_48266.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1186_48266.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1186_48266.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1186_48266.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____48169 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____48309 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48339  ->
                             match uu____48339 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____48309 with
                    | (uu____48388,us,u_let_rec_opening) ->
                        let uu___1203_48401 = lb  in
                        let uu____48402 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48405 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1203_48401.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____48402;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1203_48401.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48405;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1203_48401.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1203_48401.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term))
  =
  fun lbs  ->
    fun t  ->
      let uu____48432 =
        let uu____48440 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____48440
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____48469  ->
                 match uu____48469 with
                 | (i,out) ->
                     let uu____48492 =
                       let uu____48495 =
                         let uu____48496 =
                           let uu____48502 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____48502, i)  in
                         FStar_Syntax_Syntax.NM uu____48496  in
                       uu____48495 :: out  in
                     ((i + (Prims.parse_int "1")), uu____48492)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____48432 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____48541 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____48561  ->
                             match uu____48561 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____48541 with
                    | (uu____48592,u_let_rec_closing) ->
                        let uu___1225_48600 = lb  in
                        let uu____48601 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____48604 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1225_48600.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1225_48600.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____48601;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1225_48600.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____48604;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1225_48600.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1225_48600.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____48620  ->
      match uu____48620 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____48655  ->
                   match uu____48655 with
                   | (x,uu____48664) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____48691  ->
      match uu____48691 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____48721 = subst s t  in (us', uu____48721)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____48740  ->
      match uu____48740 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____48754 = subst s1 t  in (us, uu____48754)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____48795  ->
              match uu____48795 with
              | (x,uu____48804) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term))
  =
  fun b  ->
    fun t  ->
      let uu____48831 = open_term [b] t  in
      match uu____48831 with
      | (b1::[],t1) -> (b1, t1)
      | uu____48872 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun bvs  ->
    fun t  ->
      let uu____48903 =
        let uu____48908 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs
           in
        open_term uu____48908 t  in
      match uu____48903 with
      | (bs,t1) ->
          let uu____48923 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____48923, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun bv  ->
    fun t  ->
      let uu____48951 = open_term_bvs [bv] t  in
      match uu____48951 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____48966 -> failwith "impossible: open_term_bv"
  