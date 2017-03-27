open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk t s =
  let _0_170 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
  FStar_Syntax_Syntax.mk s _0_170 t.FStar_Syntax_Syntax.pos 
let rec inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun t  ->
      let t = FStar_Syntax_Subst.compress t  in
      let mk = mk t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____121 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_uvar _
         |FStar_Syntax_Syntax.Tm_uvar _
          |FStar_Syntax_Syntax.Tm_type _
           |FStar_Syntax_Syntax.Tm_bvar _
            |FStar_Syntax_Syntax.Tm_constant _
             |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uinst _
          -> t
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs = inst_binders s bs  in
          let body = inst s body  in
          mk
            (FStar_Syntax_Syntax.Tm_abs
               (let _0_171 = inst_lcomp_opt s lopt  in (bs, body, _0_171)))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs = inst_binders s bs  in
          let c = inst_comp s c  in mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let bv =
            let uu___159_208 = bv  in
            let _0_172 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___159_208.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___159_208.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = _0_172
            }  in
          let t = inst s t  in mk (FStar_Syntax_Syntax.Tm_refine (bv, t))
      | FStar_Syntax_Syntax.Tm_app (t,args) ->
          mk
            (FStar_Syntax_Syntax.Tm_app
               (let _0_174 = inst s t  in
                let _0_173 = inst_args s args  in (_0_174, _0_173)))
      | FStar_Syntax_Syntax.Tm_match (t,pats) ->
          let pats =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____297  ->
                    match uu____297 with
                    | (p,wopt,t) ->
                        let wopt =
                          match wopt with
                          | None  -> None
                          | Some w -> Some (inst s w)  in
                        let t = inst s t  in (p, wopt, t)))
             in
          mk
            (FStar_Syntax_Syntax.Tm_match
               (let _0_175 = inst s t  in (_0_175, pats)))
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,f) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_177 = inst s t1  in
                let _0_176 = FStar_Util.Inl (inst s t2)  in
                (_0_177, _0_176, f)))
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,f) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_179 = inst s t1  in
                let _0_178 = FStar_Util.Inr (inst_comp s c)  in
                (_0_179, _0_178, f)))
      | FStar_Syntax_Syntax.Tm_let (lbs,t) ->
          let lbs =
            let _0_182 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___160_416 = lb  in
                      let _0_181 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let _0_180 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___160_416.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___160_416.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = _0_181;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___160_416.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = _0_180
                      }))
               in
            ((Prims.fst lbs), _0_182)  in
          mk
            (FStar_Syntax_Syntax.Tm_let
               (let _0_183 = inst s t  in (lbs, _0_183)))
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern args)
          ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_185 = inst s t  in
                let _0_184 =
                  FStar_Syntax_Syntax.Meta_pattern
                    (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
                   in
                (_0_185, _0_184)))
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_188 = inst s t  in
                let _0_187 =
                  FStar_Syntax_Syntax.Meta_monadic
                    (let _0_186 = inst s t'  in (m, _0_186))
                   in
                (_0_188, _0_187)))
      | FStar_Syntax_Syntax.Tm_meta (t,tag) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_189 = inst s t  in (_0_189, tag)))

and inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____484  ->
              match uu____484 with
              | (x,imp) ->
                  let _0_191 =
                    let uu___161_491 = x  in
                    let _0_190 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___161_491.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___161_491.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = _0_190
                    }  in
                  (_0_191, imp)))

and inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____515  ->
              match uu____515 with
              | (a,imp) -> let _0_192 = inst s a  in (_0_192, imp)))

and inst_comp :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let _0_193 = inst s t  in FStar_Syntax_Syntax.mk_Total' _0_193 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let _0_194 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' _0_194 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct =
            let uu___162_550 = ct  in
            let _0_196 = inst_args s ct.FStar_Syntax_Syntax.effect_args  in
            let _0_195 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___158_553  ->
                      match uu___158_553 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          FStar_Syntax_Syntax.DECREASES (inst s t)
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (uu___162_550.FStar_Syntax_Syntax.comp_typ_name);
              FStar_Syntax_Syntax.comp_univs =
                (uu___162_550.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_args = _0_196;
              FStar_Syntax_Syntax.flags = _0_195
            }  in
          FStar_Syntax_Syntax.mk_Comp ct

and inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                 FStar_Syntax_Syntax.cflags Prims.list))
      FStar_Util.either Prims.option ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either Prims.option
  =
  fun s  ->
    fun l  ->
      match l with
      | None |Some (FStar_Util.Inr _) -> l
      | Some (FStar_Util.Inl lc) ->
          Some
            (FStar_Util.Inl
               (let uu___163_607 = lc  in
                let _0_199 = inst_args s lc.FStar_Syntax_Syntax.lcomp_indices
                   in
                let _0_198 = inst s lc.FStar_Syntax_Syntax.lcomp_res_typ  in
                {
                  FStar_Syntax_Syntax.lcomp_name =
                    (uu___163_607.FStar_Syntax_Syntax.lcomp_name);
                  FStar_Syntax_Syntax.lcomp_univs =
                    (uu___163_607.FStar_Syntax_Syntax.lcomp_univs);
                  FStar_Syntax_Syntax.lcomp_indices = _0_199;
                  FStar_Syntax_Syntax.lcomp_res_typ = _0_198;
                  FStar_Syntax_Syntax.lcomp_cflags =
                    (uu___163_607.FStar_Syntax_Syntax.lcomp_cflags);
                  FStar_Syntax_Syntax.lcomp_as_comp =
                    ((fun uu____608  ->
                        let _0_197 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                           in
                        inst_comp s _0_197))
                }))

let instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____617 ->
          let inst_fv t fv =
            let uu____625 =
              FStar_Util.find_opt
                (fun uu____631  ->
                   match uu____631 with
                   | (x,uu____635) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____625 with
            | None  -> t
            | Some (uu____642,us) ->
                mk t (FStar_Syntax_Syntax.Tm_uinst (t, us))
             in
          inst inst_fv t
  