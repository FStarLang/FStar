open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)
let report :
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit =
  fun env  ->
    fun errs  ->
      let uu____12 = FStar_TypeChecker_Env.get_range env  in
      let uu____13 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.report uu____12 uu____13
  
let is_type : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____17 =
      let uu____18 = FStar_Syntax_Subst.compress t  in
      uu____18.FStar_Syntax_Syntax.n  in
    match uu____17 with
    | FStar_Syntax_Syntax.Tm_type uu____21 -> true
    | uu____22 -> false
  
let t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    let uu____29 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right uu____29
      (FStar_List.filter
         (fun uu____35  ->
            match uu____35 with
            | (x,uu____39) -> is_type x.FStar_Syntax_Syntax.sort))
  
let new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____49 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____50 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____50)
           in
        if uu____49
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let uu____52 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Env.new_uvar uu____52 bs k
  
let new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun k  -> let uu____59 = new_uvar_aux env k  in Prims.fst uu____59
  
let as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar =
  fun uu___92_64  ->
    match uu___92_64 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____66);
        FStar_Syntax_Syntax.tk = uu____67;
        FStar_Syntax_Syntax.pos = uu____68;
        FStar_Syntax_Syntax.vars = uu____69;_} -> uv
    | uu____84 -> failwith "Impossible"
  
let new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____103 =
            FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid  in
          match uu____103 with
          | Some (uu____116::(tm,uu____118)::[]) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))))
                  None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____162 ->
              let uu____169 = new_uvar_aux env k  in
              (match uu____169 with
               | (t,u) ->
                   let g =
                     let uu___112_181 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____182 =
                       let uu____190 =
                         let uu____197 = as_uvar u  in
                         (reason, env, uu____197, t, k, r)  in
                       [uu____190]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___112_181.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___112_181.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___112_181.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____182
                     }  in
                   let uu____210 =
                     let uu____214 =
                       let uu____217 = as_uvar u  in (uu____217, r)  in
                     [uu____214]  in
                   (t, uu____210, g))
  
let check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____235 =
        let uu____236 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____236  in
      if uu____235
      then
        let us =
          let uu____240 =
            let uu____242 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____258  ->
                 match uu____258 with
                 | (x,uu____266) -> FStar_Syntax_Print.uvar_to_string x)
              uu____242
             in
          FStar_All.pipe_right uu____240 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____283 =
            let uu____284 = FStar_Syntax_Print.term_to_string t  in
            FStar_Util.format2
              "Unconstrained unification variables %s in type signature %s; please add an annotation"
              us uu____284
             in
          FStar_Errors.report r uu____283);
         FStar_Options.pop ())
      else ()
  
let force_sort' :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term'
  =
  fun s  ->
    let uu____293 = FStar_ST.read s.FStar_Syntax_Syntax.tk  in
    match uu____293 with
    | None  ->
        let uu____298 =
          let uu____299 =
            FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos  in
          let uu____300 = FStar_Syntax_Print.term_to_string s  in
          FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s"
            uu____299 uu____300
           in
        failwith uu____298
    | Some tk -> tk
  
let force_sort s =
  let uu____315 =
    let uu____318 = force_sort' s  in FStar_Syntax_Syntax.mk uu____318  in
  uu____315 None s.FStar_Syntax_Syntax.pos 
let extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.typ *
        Prims.bool)
  =
  fun env  ->
    fun uu____335  ->
      match uu____335 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____342;
          FStar_Syntax_Syntax.lbdef = e;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars1 <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let mk_binder1 scope a =
                   let uu____374 =
                     let uu____375 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort
                        in
                     uu____375.FStar_Syntax_Syntax.n  in
                   match uu____374 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____380 = FStar_Syntax_Util.type_u ()  in
                       (match uu____380 with
                        | (k,uu____386) ->
                            let t2 =
                              let uu____388 =
                                FStar_TypeChecker_Env.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right uu____388 Prims.fst  in
                            ((let uu___113_393 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___113_393.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___113_393.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____394 -> (a, true)  in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1  in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____419) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____426) ->
                       (t2, true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____453) ->
                       let uu____476 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____500  ->
                                 fun uu____501  ->
                                   match (uu____500, uu____501) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____543 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a  in
                                       (match uu____543 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp)  in
                                            let bs2 =
                                              FStar_List.append bs1 [b]  in
                                            let scope1 =
                                              FStar_List.append scope [b]  in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____476 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____604 = aux must_check_ty1 scope body  in
                            (match uu____604 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____621 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____621
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c  in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c  in
                                 ((let uu____626 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____626
                                   then
                                     let uu____627 =
                                       FStar_Range.string_of_range r  in
                                     let uu____628 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____629 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____627 uu____628 uu____629
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____633 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____641 =
                            let uu____644 =
                              let uu____645 =
                                FStar_TypeChecker_Env.new_uvar r vars
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____645 Prims.fst  in
                            FStar_Util.Inl uu____644  in
                          (uu____641, false))
                    in
                 let uu____652 =
                   let uu____657 = t_binders env  in aux false uu____657 e
                    in
                 match uu____652 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____670 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____670
                           then FStar_TypeChecker_Env.result_typ env c
                           else
                             (let uu____672 =
                                let uu____673 =
                                  let uu____676 =
                                    let uu____677 =
                                      FStar_Syntax_Print.comp_to_string c  in
                                    FStar_Util.format1
                                      "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                      uu____677
                                     in
                                  (uu____676, rng)  in
                                FStar_Errors.Error uu____673  in
                              Prims.raise uu____672)
                       | FStar_Util.Inl t3 -> t3  in
                     ([], t3, b)))
           | uu____680 ->
               let uu____681 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____681 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let pat_as_exps :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term
          Prims.list * FStar_Syntax_Syntax.pat)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
                  None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____764) ->
              let uu____769 = FStar_Syntax_Util.type_u ()  in
              (match uu____769 with
               | (k,uu____782) ->
                   let t = new_uvar env1 k  in
                   let x1 =
                     let uu___114_785 = x  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___114_785.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___114_785.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = t
                     }  in
                   let uu____786 =
                     let uu____789 = FStar_TypeChecker_Env.all_binders env1
                        in
                     FStar_TypeChecker_Env.new_uvar p1.FStar_Syntax_Syntax.p
                       uu____789 t
                      in
                   (match uu____786 with
                    | (e,u) ->
                        let p2 =
                          let uu___115_804 = p1  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                            FStar_Syntax_Syntax.ty =
                              (uu___115_804.FStar_Syntax_Syntax.ty);
                            FStar_Syntax_Syntax.p =
                              (uu___115_804.FStar_Syntax_Syntax.p)
                          }  in
                        ([], [], [], env1, e, p2)))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____811 = FStar_Syntax_Util.type_u ()  in
              (match uu____811 with
               | (t,uu____824) ->
                   let x1 =
                     let uu___116_826 = x  in
                     let uu____827 = new_uvar env1 t  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___116_826.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___116_826.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____827
                     }  in
                   let env2 =
                     if allow_wc_dependence
                     then FStar_TypeChecker_Env.push_bv env1 x1
                     else env1  in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____849 = FStar_Syntax_Util.type_u ()  in
              (match uu____849 with
               | (t,uu____862) ->
                   let x1 =
                     let uu___117_864 = x  in
                     let uu____865 = new_uvar env1 t  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___117_864.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___117_864.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____865
                     }  in
                   let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                   let e =
                     (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1))
                       None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____897 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____953  ->
                        fun uu____954  ->
                          match (uu____953, uu____954) with
                          | ((b,a,w,env2,args,pats1),(p2,imp)) ->
                              let uu____1053 =
                                pat_as_arg_with_env allow_wc_dependence env2
                                  p2
                                 in
                              (match uu____1053 with
                               | (b',a',w',env3,te,pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), ((pat, imp) :: pats1))))
                     ([], [], [], env1, [], []))
                 in
              (match uu____897 with
               | (b,a,w,env2,args,pats1) ->
                   let e =
                     let uu____1161 =
                       let uu____1164 =
                         let uu____1165 =
                           let uu____1170 =
                             let uu____1173 =
                               let uu____1174 =
                                 FStar_Syntax_Syntax.fv_to_tm fv  in
                               let uu____1175 =
                                 FStar_All.pipe_right args FStar_List.rev  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____1174
                                 uu____1175
                                in
                             uu____1173 None p1.FStar_Syntax_Syntax.p  in
                           (uu____1170,
                             (FStar_Syntax_Syntax.Meta_desugared
                                FStar_Syntax_Syntax.Data_app))
                            in
                         FStar_Syntax_Syntax.Tm_meta uu____1165  in
                       FStar_Syntax_Syntax.mk uu____1164  in
                     uu____1161 None p1.FStar_Syntax_Syntax.p  in
                   let uu____1192 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____1198 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____1204 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____1192, uu____1198, uu____1204, env2, e,
                     (let uu___118_1217 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.ty =
                          (uu___118_1217.FStar_Syntax_Syntax.ty);
                        FStar_Syntax_Syntax.p =
                          (uu___118_1217.FStar_Syntax_Syntax.p)
                      })))
          | FStar_Syntax_Syntax.Pat_disj uu____1223 -> failwith "impossible"
           in
        let rec elaborate_pat env1 p1 =
          let maybe_dot inaccessible a r =
            if allow_implicits && inaccessible
            then
              FStar_Syntax_Syntax.withinfo
                (FStar_Syntax_Syntax.Pat_dot_term
                   (a, FStar_Syntax_Syntax.tun))
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
            else
              FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
             in
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let pats1 =
                FStar_List.map
                  (fun uu____1292  ->
                     match uu____1292 with
                     | (p2,imp) ->
                         let uu____1307 = elaborate_pat env1 p2  in
                         (uu____1307, imp)) pats
                 in
              let uu____1312 =
                FStar_TypeChecker_Env.lookup_datacon env1
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              (match uu____1312 with
               | (uu____1321,t) ->
                   let uu____1323 = FStar_Syntax_Util.arrow_formals_comp t
                      in
                   (match uu____1323 with
                    | (f,uu____1332) ->
                        let rec aux formals pats2 =
                          match (formals, pats2) with
                          | ([],[]) -> []
                          | ([],uu____1403::uu____1404) ->
                              Prims.raise
                                (FStar_Errors.Error
                                   ("Too many pattern arguments",
                                     (FStar_Ident.range_of_lid
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                          | (uu____1439::uu____1440,[]) ->
                              FStar_All.pipe_right formals
                                (FStar_List.map
                                   (fun uu____1480  ->
                                      match uu____1480 with
                                      | (t1,imp) ->
                                          (match imp with
                                           | Some
                                               (FStar_Syntax_Syntax.Implicit
                                               inaccessible) ->
                                               let a =
                                                 let uu____1498 =
                                                   let uu____1500 =
                                                     FStar_Syntax_Syntax.range_of_bv
                                                       t1
                                                      in
                                                   Some uu____1500  in
                                                 FStar_Syntax_Syntax.new_bv
                                                   uu____1498
                                                   FStar_Syntax_Syntax.tun
                                                  in
                                               let r =
                                                 FStar_Ident.range_of_lid
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                  in
                                               let uu____1506 =
                                                 maybe_dot inaccessible a r
                                                  in
                                               (uu____1506, true)
                                           | uu____1511 ->
                                               let uu____1513 =
                                                 let uu____1514 =
                                                   let uu____1517 =
                                                     let uu____1518 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1518
                                                      in
                                                   (uu____1517,
                                                     (FStar_Ident.range_of_lid
                                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                                                    in
                                                 FStar_Errors.Error
                                                   uu____1514
                                                  in
                                               Prims.raise uu____1513)))
                          | (f1::formals',(p2,p_imp)::pats') ->
                              (match f1 with
                               | (uu____1569,Some
                                  (FStar_Syntax_Syntax.Implicit uu____1570))
                                   when p_imp ->
                                   let uu____1572 = aux formals' pats'  in
                                   (p2, true) :: uu____1572
                               | (uu____1584,Some
                                  (FStar_Syntax_Syntax.Implicit
                                  inaccessible)) ->
                                   let a =
                                     FStar_Syntax_Syntax.new_bv
                                       (Some (p2.FStar_Syntax_Syntax.p))
                                       FStar_Syntax_Syntax.tun
                                      in
                                   let p3 =
                                     maybe_dot inaccessible a
                                       (FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                      in
                                   let uu____1595 = aux formals' pats2  in
                                   (p3, true) :: uu____1595
                               | (uu____1607,imp) ->
                                   let uu____1611 =
                                     let uu____1616 =
                                       FStar_Syntax_Syntax.is_implicit imp
                                        in
                                     (p2, uu____1616)  in
                                   let uu____1619 = aux formals' pats'  in
                                   uu____1611 :: uu____1619)
                           in
                        let uu___119_1629 = p1  in
                        let uu____1632 =
                          let uu____1633 =
                            let uu____1641 = aux f pats1  in (fv, uu____1641)
                             in
                          FStar_Syntax_Syntax.Pat_cons uu____1633  in
                        {
                          FStar_Syntax_Syntax.v = uu____1632;
                          FStar_Syntax_Syntax.ty =
                            (uu___119_1629.FStar_Syntax_Syntax.ty);
                          FStar_Syntax_Syntax.p =
                            (uu___119_1629.FStar_Syntax_Syntax.p)
                        }))
          | uu____1652 -> p1  in
        let one_pat allow_wc_dependence env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____1678 = pat_as_arg_with_env allow_wc_dependence env1 p2
             in
          match uu____1678 with
          | (b,a,w,env2,arg,p3) ->
              let uu____1708 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1708 with
               | Some x ->
                   let uu____1721 =
                     let uu____1722 =
                       let uu____1725 =
                         FStar_TypeChecker_Err.nonlinear_pattern_variable x
                          in
                       (uu____1725, (p3.FStar_Syntax_Syntax.p))  in
                     FStar_Errors.Error uu____1722  in
                   Prims.raise uu____1721
               | uu____1734 -> (b, a, w, arg, p3))
           in
        let top_level_pat_as_args env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_disj [] -> failwith "impossible"
          | FStar_Syntax_Syntax.Pat_disj (q::pats) ->
              let uu____1777 = one_pat false env1 q  in
              (match uu____1777 with
               | (b,a,uu____1793,te,q1) ->
                   let uu____1802 =
                     FStar_List.fold_right
                       (fun p2  ->
                          fun uu____1818  ->
                            match uu____1818 with
                            | (w,args,pats1) ->
                                let uu____1842 = one_pat false env1 p2  in
                                (match uu____1842 with
                                 | (b',a',w',arg,p3) ->
                                     let uu____1868 =
                                       let uu____1869 =
                                         FStar_Util.multiset_equiv
                                           FStar_Syntax_Syntax.bv_eq a a'
                                          in
                                       Prims.op_Negation uu____1869  in
                                     if uu____1868
                                     then
                                       let uu____1876 =
                                         let uu____1877 =
                                           let uu____1880 =
                                             FStar_TypeChecker_Err.disjunctive_pattern_vars
                                               a a'
                                              in
                                           let uu____1881 =
                                             FStar_TypeChecker_Env.get_range
                                               env1
                                              in
                                           (uu____1880, uu____1881)  in
                                         FStar_Errors.Error uu____1877  in
                                       Prims.raise uu____1876
                                     else
                                       (let uu____1889 =
                                          let uu____1891 =
                                            FStar_Syntax_Syntax.as_arg arg
                                             in
                                          uu____1891 :: args  in
                                        ((FStar_List.append w' w),
                                          uu____1889, (p3 :: pats1))))) pats
                       ([], [], [])
                      in
                   (match uu____1802 with
                    | (w,args,pats1) ->
                        let uu____1912 =
                          let uu____1914 = FStar_Syntax_Syntax.as_arg te  in
                          uu____1914 :: args  in
                        ((FStar_List.append b w), uu____1912,
                          (let uu___120_1919 = p1  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_disj (q1 :: pats1));
                             FStar_Syntax_Syntax.ty =
                               (uu___120_1919.FStar_Syntax_Syntax.ty);
                             FStar_Syntax_Syntax.p =
                               (uu___120_1919.FStar_Syntax_Syntax.p)
                           }))))
          | uu____1920 ->
              let uu____1921 = one_pat true env1 p1  in
              (match uu____1921 with
               | (b,uu____1936,uu____1937,arg,p2) ->
                   let uu____1946 =
                     let uu____1948 = FStar_Syntax_Syntax.as_arg arg  in
                     [uu____1948]  in
                   (b, uu____1946, p2))
           in
        let uu____1951 = top_level_pat_as_args env p  in
        match uu____1951 with
        | (b,args,p1) ->
            let exps = FStar_All.pipe_right args (FStar_List.map Prims.fst)
               in
            (b, exps, p1)
  
let decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.pat
  =
  fun env  ->
    fun p  ->
      fun exps  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q t =
            FStar_Syntax_Syntax.withinfo q t p1.FStar_Syntax_Syntax.p  in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2022,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2024)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant
             uu____2029,FStar_Syntax_Syntax.Tm_constant uu____2030) ->
              let uu____2031 = force_sort' e1  in
              pkg p1.FStar_Syntax_Syntax.v uu____2031
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2035 =
                    let uu____2036 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2037 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2036 uu____2037
                     in
                  failwith uu____2035)
               else ();
               (let uu____2040 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2040
                then
                  let uu____2041 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2042 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2041
                    uu____2042
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___121_2046 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___121_2046.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___121_2046.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2050 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2050
                then
                  let uu____2051 =
                    let uu____2052 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2053 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2052 uu____2053
                     in
                  failwith uu____2051
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___122_2057 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___122_2057.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___122_2057.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1) s.FStar_Syntax_Syntax.n))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2059),uu____2060) ->
              let s = force_sort e1  in
              let x1 =
                let uu___123_2069 = x  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___123_2069.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___123_2069.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = s
                }  in
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x1, e1))
                s.FStar_Syntax_Syntax.n
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2082 =
                  let uu____2083 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2083  in
                if uu____2082
                then
                  let uu____2084 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2084
                else ());
               (let uu____2094 = force_sort' e1  in
                pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])) uu____2094))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                FStar_Syntax_Syntax.vars = _;_},args))
            |(FStar_Syntax_Syntax.Pat_cons
              (fv,argpats),FStar_Syntax_Syntax.Tm_app
              ({
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                   ({
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_);
                 FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                 FStar_Syntax_Syntax.vars = _;_},args))
              ->
              ((let uu____2165 =
                  let uu____2166 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2166 Prims.op_Negation  in
                if uu____2165
                then
                  let uu____2167 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2167
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      let uu____2255 = force_sort' e1  in
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats))) uu____2255
                  | (arg::args2,(argpat,uu____2268)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,Some (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____2318) ->
                           let x =
                             let uu____2334 = force_sort e2  in
                             FStar_Syntax_Syntax.new_bv
                               (Some (p1.FStar_Syntax_Syntax.p)) uu____2334
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____2348) ->
                           let pat =
                             let uu____2363 = aux argpat e2  in
                             let uu____2364 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____2363, uu____2364)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____2367 ->
                      let uu____2381 =
                        let uu____2382 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____2383 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____2382 uu____2383
                         in
                      failwith uu____2381
                   in
                match_args [] args argpats))
          | uu____2390 ->
              let uu____2393 =
                let uu____2394 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____2395 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____2396 =
                  let uu____2397 =
                    FStar_All.pipe_right exps
                      (FStar_List.map FStar_Syntax_Print.term_to_string)
                     in
                  FStar_All.pipe_right uu____2397
                    (FStar_String.concat "\n\t")
                   in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____2394 uu____2395 uu____2396
                 in
              failwith uu____2393
           in
        match ((p.FStar_Syntax_Syntax.v), exps) with
        | (FStar_Syntax_Syntax.Pat_disj ps,uu____2404) when
            (FStar_List.length ps) = (FStar_List.length exps) ->
            let ps1 = FStar_List.map2 aux ps exps  in
            FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj ps1)
              FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
              p.FStar_Syntax_Syntax.p
        | (uu____2420,e::[]) -> aux p e
        | uu____2423 -> failwith "Unexpected number of patterns"
  
let rec decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term)
  =
  fun pat  ->
    let topt = Some (pat.FStar_Syntax_Syntax.ty)  in
    let mk1 f = (FStar_Syntax_Syntax.mk f) topt pat.FStar_Syntax_Syntax.p  in
    let pat_as_arg uu____2460 =
      match uu____2460 with
      | (p,i) ->
          let uu____2470 = decorated_pattern_as_term p  in
          (match uu____2470 with
           | (vars,te) ->
               let uu____2483 =
                 let uu____2486 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____2486)  in
               (vars, uu____2483))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_disj uu____2493 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____2501 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____2501)
    | FStar_Syntax_Syntax.Pat_wild x|FStar_Syntax_Syntax.Pat_var x ->
        let uu____2504 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____2504)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____2518 =
          let uu____2526 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____2526 FStar_List.unzip  in
        (match uu____2518 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____2584 =
               let uu____2585 =
                 let uu____2586 =
                   let uu____2596 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____2596, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____2586  in
               mk1 uu____2585  in
             (vars1, uu____2584))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let arrow_formals :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____2620 = FStar_Syntax_Util.arrow_formals_comp k  in
      match uu____2620 with
      | (bs,c) ->
          let uu____2636 = FStar_TypeChecker_Env.result_typ env c  in
          (bs, uu____2636)
  
let join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____2649 =
          let uu____2653 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____2654 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____2653 uu____2654  in
        match uu____2649 with | (m,uu____2656,uu____2657) -> m
  
let lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        (FStar_TypeChecker_Env.normal_comp_typ *
          FStar_TypeChecker_Env.normal_comp_typ)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c1  in
        let c21 = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c2  in
        let uu____2671 =
          FStar_TypeChecker_Env.join env c11.FStar_TypeChecker_Env.nct_name
            c21.FStar_TypeChecker_Env.nct_name
           in
        match uu____2671 with
        | (m,lift1,lift2) ->
            let uu____2680 = lift1 c11  in
            let uu____2682 = lift2 c21  in (uu____2680, uu____2682)
  
let force_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____2693 = FStar_TypeChecker_Rel.teq env t1 t2  in
        FStar_TypeChecker_Rel.force_trivial_guard env uu____2693
  
let join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.lcomp * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc1  ->
      fun lc2  ->
        let uu____2705 =
          (FStar_Syntax_Util.is_total_lcomp lc1) &&
            (FStar_Syntax_Util.is_total_lcomp lc2)
           in
        if uu____2705
        then (lc1, lc2)
        else
          (let nct_of_lcomp lc =
             let uu____2713 =
               FStar_Syntax_Syntax.as_arg
                 lc.FStar_Syntax_Syntax.lcomp_res_typ
                in
             let uu____2714 =
               FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun  in
             {
               FStar_TypeChecker_Env.nct_name =
                 (lc.FStar_Syntax_Syntax.lcomp_name);
               FStar_TypeChecker_Env.nct_univs =
                 (lc.FStar_Syntax_Syntax.lcomp_univs);
               FStar_TypeChecker_Env.nct_indices =
                 (lc.FStar_Syntax_Syntax.lcomp_indices);
               FStar_TypeChecker_Env.nct_result = uu____2713;
               FStar_TypeChecker_Env.nct_wp = uu____2714;
               FStar_TypeChecker_Env.nct_flags =
                 (lc.FStar_Syntax_Syntax.lcomp_cflags)
             }  in
           let lcomp_of_nct nct =
             {
               FStar_Syntax_Syntax.lcomp_name =
                 (nct.FStar_TypeChecker_Env.nct_name);
               FStar_Syntax_Syntax.lcomp_univs =
                 (nct.FStar_TypeChecker_Env.nct_univs);
               FStar_Syntax_Syntax.lcomp_indices =
                 (nct.FStar_TypeChecker_Env.nct_indices);
               FStar_Syntax_Syntax.lcomp_res_typ =
                 (Prims.fst nct.FStar_TypeChecker_Env.nct_result);
               FStar_Syntax_Syntax.lcomp_cflags =
                 (nct.FStar_TypeChecker_Env.nct_flags);
               FStar_Syntax_Syntax.lcomp_as_comp =
                 (fun uu____2721  ->
                    FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct)
             }  in
           let uu____2722 =
             FStar_TypeChecker_Env.join env
               lc1.FStar_Syntax_Syntax.lcomp_name
               lc2.FStar_Syntax_Syntax.lcomp_name
              in
           match uu____2722 with
           | (uu____2728,lift1,lift2) ->
               let nct1 =
                 let uu____2732 = nct_of_lcomp lc1  in lift1 uu____2732  in
               let nct2 =
                 let uu____2735 = nct_of_lcomp lc2  in lift2 uu____2735  in
               ((let uu____2738 =
                   FStar_List.tl nct1.FStar_TypeChecker_Env.nct_univs  in
                 let uu____2740 =
                   FStar_List.tl nct2.FStar_TypeChecker_Env.nct_univs  in
                 FStar_List.iter2
                   (fun u  ->
                      fun v1  ->
                        let uu____2744 = FStar_Syntax_Util.type_at_u u  in
                        let uu____2745 = FStar_Syntax_Util.type_at_u v1  in
                        force_teq env uu____2744 uu____2745) uu____2738
                   uu____2740);
                FStar_List.iter2
                  (fun uu____2751  ->
                     fun uu____2752  ->
                       match (uu____2751, uu____2752) with
                       | ((i,uu____2762),(j,uu____2764)) -> force_teq env i j)
                  nct1.FStar_TypeChecker_Env.nct_indices
                  nct2.FStar_TypeChecker_Env.nct_indices;
                ((lcomp_of_nct nct1), (lcomp_of_nct nct2))))
  
let is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid
  
let is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid)
  
let mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universes ->
      FStar_Syntax_Syntax.arg Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  =
  fun mname  ->
    fun univs1  ->
      fun indices  ->
        fun result  ->
          fun wp  ->
            fun flags  ->
              let uu____2805 =
                let uu____2806 =
                  let uu____2812 =
                    let uu____2814 = FStar_Syntax_Syntax.as_arg result  in
                    let uu____2815 =
                      let uu____2817 = FStar_Syntax_Syntax.as_arg wp  in
                      [uu____2817]  in
                    uu____2814 :: uu____2815  in
                  FStar_List.append indices uu____2812  in
                {
                  FStar_Syntax_Syntax.comp_typ_name = mname;
                  FStar_Syntax_Syntax.comp_univs = univs1;
                  FStar_Syntax_Syntax.effect_args = uu____2806;
                  FStar_Syntax_Syntax.flags = flags
                }  in
              FStar_Syntax_Syntax.mk_Comp uu____2805
  
let mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universes ->
      FStar_Syntax_Syntax.arg Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let subst_lcomp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun subst1  ->
    fun lc  ->
      let uu___124_2841 = lc  in
      let uu____2842 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.lcomp_res_typ
         in
      {
        FStar_Syntax_Syntax.lcomp_name =
          (uu___124_2841.FStar_Syntax_Syntax.lcomp_name);
        FStar_Syntax_Syntax.lcomp_univs =
          (uu___124_2841.FStar_Syntax_Syntax.lcomp_univs);
        FStar_Syntax_Syntax.lcomp_indices =
          (uu___124_2841.FStar_Syntax_Syntax.lcomp_indices);
        FStar_Syntax_Syntax.lcomp_res_typ = uu____2842;
        FStar_Syntax_Syntax.lcomp_cflags =
          (uu___124_2841.FStar_Syntax_Syntax.lcomp_cflags);
        FStar_Syntax_Syntax.lcomp_as_comp =
          (fun uu____2845  ->
             let uu____2846 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
             FStar_Syntax_Subst.subst_comp subst1 uu____2846)
      }
  
let is_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2850 =
      let uu____2851 = FStar_Syntax_Subst.compress t  in
      uu____2851.FStar_Syntax_Syntax.n  in
    match uu____2850 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2854 -> true
    | uu____2862 -> false
  
let return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun t  ->
      fun v1  ->
        let c =
          let uu____2873 =
            let uu____2874 =
              FStar_TypeChecker_Env.lid_exists env
                FStar_Syntax_Const.effect_GTot_lid
               in
            FStar_All.pipe_left Prims.op_Negation uu____2874  in
          if uu____2873
          then FStar_Syntax_Syntax.mk_Total t
          else
            (let m =
               let uu____2877 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   FStar_Syntax_Const.effect_PURE_lid
                  in
               FStar_Util.must uu____2877  in
             let u_t = env.FStar_TypeChecker_Env.universe_of env t  in
             let wp =
               let uu____2881 =
                 env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                  in
               if uu____2881
               then FStar_Syntax_Syntax.tun
               else
                 (let uu____2883 =
                    FStar_TypeChecker_Env.wp_signature env
                      FStar_Syntax_Const.effect_PURE_lid
                     in
                  match uu____2883 with
                  | (a,kwp) ->
                      let k =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT (a, t)] kwp
                         in
                      let uu____2889 =
                        let uu____2890 =
                          let uu____2891 =
                            FStar_TypeChecker_Env.inst_effect_fun_with 
                              [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                             in
                          let uu____2892 =
                            let uu____2893 = FStar_Syntax_Syntax.as_arg t  in
                            let uu____2894 =
                              let uu____2896 = FStar_Syntax_Syntax.as_arg v1
                                 in
                              [uu____2896]  in
                            uu____2893 :: uu____2894  in
                          FStar_Syntax_Syntax.mk_Tm_app uu____2891 uu____2892
                           in
                        uu____2890 (Some (k.FStar_Syntax_Syntax.n))
                          v1.FStar_Syntax_Syntax.pos
                         in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta] env uu____2889)
                in
             (mk_comp m) [u_t] [] t wp [FStar_Syntax_Syntax.RETURN])
           in
        (let uu____2902 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Return")
            in
         if uu____2902
         then
           let uu____2903 =
             FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
           let uu____2904 = FStar_Syntax_Print.term_to_string v1  in
           let uu____2905 = FStar_TypeChecker_Normalize.comp_to_string env c
              in
           FStar_Util.print3 "(%s) returning %s at comp type %s\n" uu____2903
             uu____2904 uu____2905
         else ());
        c
  
let bind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.lcomp ->
        lcomp_with_binder -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e1opt  ->
      fun lc1  ->
        fun uu____2919  ->
          match uu____2919 with
          | (b,lc2) ->
              let lc11 =
                FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
              let lc21 =
                FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
              ((let uu____2928 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                if uu____2928
                then
                  let bstr =
                    match b with
                    | None  -> "none"
                    | Some x -> FStar_Syntax_Print.bv_to_string x  in
                  let uu____2931 =
                    match e1opt with
                    | None  -> "None"
                    | Some e -> FStar_Syntax_Print.term_to_string e  in
                  let uu____2933 = FStar_Syntax_Print.lcomp_to_string lc11
                     in
                  let uu____2934 = FStar_Syntax_Print.lcomp_to_string lc21
                     in
                  FStar_Util.print4
                    "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n"
                    uu____2931 uu____2933 bstr uu____2934
                else ());
               (let uu____2936 = join_lcomp env lc11 lc21  in
                match uu____2936 with
                | (lc12,lc22) ->
                    let bind_it uu____2944 =
                      let c1 = lc12.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                      let c2 = lc22.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                      (let uu____2952 =
                         FStar_TypeChecker_Env.debug env
                           FStar_Options.Extreme
                          in
                       if uu____2952
                       then
                         let uu____2953 =
                           match b with
                           | None  -> "none"
                           | Some x -> FStar_Syntax_Print.bv_to_string x  in
                         let uu____2955 =
                           FStar_Syntax_Print.lcomp_to_string lc12  in
                         let uu____2956 =
                           FStar_Syntax_Print.comp_to_string c1  in
                         let uu____2957 =
                           FStar_Syntax_Print.lcomp_to_string lc22  in
                         let uu____2958 =
                           FStar_Syntax_Print.comp_to_string c2  in
                         FStar_Util.print5
                           "b=%s,Evaluated %s to %s\n And %s to %s\n"
                           uu____2953 uu____2955 uu____2956 uu____2957
                           uu____2958
                       else ());
                      (let try_simplify uu____2966 =
                         let aux uu____2975 =
                           let uu____2976 =
                             FStar_Syntax_Util.is_trivial_wp c1  in
                           if uu____2976
                           then
                             match b with
                             | None  -> Some (c2, "trivial no binder")
                             | Some uu____2993 ->
                                 let uu____2994 =
                                   FStar_Syntax_Util.is_ml_comp c2  in
                                 (if uu____2994
                                  then Some (c2, "trivial ml")
                                  else None)
                           else
                             (let uu____3012 =
                                (FStar_Syntax_Util.is_ml_comp c1) &&
                                  (FStar_Syntax_Util.is_ml_comp c2)
                                 in
                              if uu____3012
                              then Some (c2, "both ml")
                              else None)
                            in
                         let subst_c2 reason =
                           match (e1opt, b) with
                           | (Some e,Some x) ->
                               let uu____3045 =
                                 let uu____3048 =
                                   FStar_Syntax_Subst.subst_comp
                                     [FStar_Syntax_Syntax.NT (x, e)] c2
                                    in
                                 (uu____3048, reason)  in
                               Some uu____3045
                           | uu____3051 -> aux ()  in
                         let uu____3056 =
                           (FStar_Syntax_Util.is_total_comp c1) &&
                             (FStar_Syntax_Util.is_total_comp c2)
                            in
                         if uu____3056
                         then subst_c2 "both total"
                         else
                           (let uu____3061 =
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                               in
                            if uu____3061
                            then
                              let uu____3065 =
                                let uu____3068 =
                                  let uu____3069 =
                                    FStar_TypeChecker_Env.result_typ env c2
                                     in
                                  FStar_Syntax_Syntax.mk_GTotal uu____3069
                                   in
                                (uu____3068, "both gtot")  in
                              Some uu____3065
                            else
                              (match (e1opt, b) with
                               | (Some e,Some x) ->
                                   let uu____3082 =
                                     (FStar_Syntax_Util.is_total_comp c1) &&
                                       (let uu____3083 =
                                          FStar_Syntax_Syntax.is_null_bv x
                                           in
                                        Prims.op_Negation uu____3083)
                                      in
                                   if uu____3082
                                   then subst_c2 "substituted e"
                                   else aux ()
                               | uu____3088 -> aux ()))
                          in
                       let uu____3093 = try_simplify ()  in
                       match uu____3093 with
                       | Some (c,reason) -> c
                       | None  ->
                           let nct1 =
                             FStar_TypeChecker_Env.comp_as_normal_comp_typ
                               env c1
                              in
                           let nct2 =
                             FStar_TypeChecker_Env.comp_as_normal_comp_typ
                               env c2
                              in
                           let md =
                             FStar_TypeChecker_Env.get_effect_decl env
                               nct1.FStar_TypeChecker_Env.nct_name
                              in
                           let t1 =
                             Prims.fst nct1.FStar_TypeChecker_Env.nct_result
                              in
                           let t2 =
                             Prims.fst nct2.FStar_TypeChecker_Env.nct_result
                              in
                           let mk_lam wp =
                             let bs =
                               match b with
                               | None  ->
                                   let uu____3123 =
                                     FStar_Syntax_Syntax.null_binder
                                       (Prims.fst
                                          nct1.FStar_TypeChecker_Env.nct_result)
                                      in
                                   [uu____3123]
                               | Some x ->
                                   let uu____3127 =
                                     FStar_Syntax_Syntax.mk_binder x  in
                                   [uu____3127]
                                in
                             FStar_Syntax_Util.abs bs wp
                               (Some
                                  (FStar_Util.Inr
                                     (FStar_Syntax_Const.effect_Tot_lid,
                                       [FStar_Syntax_Syntax.TOTAL])))
                              in
                           let bind_inst =
                             let uu____3138 =
                               let uu____3139 =
                                 let uu____3141 =
                                   FStar_List.hd
                                     nct2.FStar_TypeChecker_Env.nct_univs
                                    in
                                 [uu____3141]  in
                               FStar_List.append
                                 nct1.FStar_TypeChecker_Env.nct_univs
                                 uu____3139
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               uu____3138 env md
                               md.FStar_Syntax_Syntax.bind_wp
                              in
                           let bind_args =
                             let uu____3148 =
                               let uu____3154 =
                                 let uu____3156 =
                                   let uu____3158 =
                                     let uu____3160 =
                                       let uu____3161 =
                                         mk_lam
                                           (Prims.fst
                                              nct2.FStar_TypeChecker_Env.nct_wp)
                                          in
                                       FStar_Syntax_Syntax.as_arg uu____3161
                                        in
                                     [uu____3160]  in
                                   (nct1.FStar_TypeChecker_Env.nct_wp) ::
                                     uu____3158
                                    in
                                 (nct2.FStar_TypeChecker_Env.nct_result) ::
                                   uu____3156
                                  in
                               (nct1.FStar_TypeChecker_Env.nct_result) ::
                                 uu____3154
                                in
                             FStar_List.append
                               nct1.FStar_TypeChecker_Env.nct_indices
                               uu____3148
                              in
                           let wp =
                             (FStar_Syntax_Syntax.mk_Tm_app bind_inst
                                bind_args) None t2.FStar_Syntax_Syntax.pos
                              in
                           let nct =
                             let uu___125_3176 = nct2  in
                             let uu____3177 = FStar_Syntax_Syntax.as_arg wp
                                in
                             {
                               FStar_TypeChecker_Env.nct_name =
                                 (uu___125_3176.FStar_TypeChecker_Env.nct_name);
                               FStar_TypeChecker_Env.nct_univs =
                                 (uu___125_3176.FStar_TypeChecker_Env.nct_univs);
                               FStar_TypeChecker_Env.nct_indices =
                                 (uu___125_3176.FStar_TypeChecker_Env.nct_indices);
                               FStar_TypeChecker_Env.nct_result =
                                 (uu___125_3176.FStar_TypeChecker_Env.nct_result);
                               FStar_TypeChecker_Env.nct_wp = uu____3177;
                               FStar_TypeChecker_Env.nct_flags =
                                 (uu___125_3176.FStar_TypeChecker_Env.nct_flags)
                             }  in
                           FStar_TypeChecker_Env.normal_comp_typ_as_comp env
                             nct)
                       in
                    let uu____3178 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3178
                    then lc22
                    else
                      (let uu___126_3180 = lc22  in
                       {
                         FStar_Syntax_Syntax.lcomp_name =
                           (uu___126_3180.FStar_Syntax_Syntax.lcomp_name);
                         FStar_Syntax_Syntax.lcomp_univs =
                           (uu___126_3180.FStar_Syntax_Syntax.lcomp_univs);
                         FStar_Syntax_Syntax.lcomp_indices =
                           (uu___126_3180.FStar_Syntax_Syntax.lcomp_indices);
                         FStar_Syntax_Syntax.lcomp_res_typ =
                           (uu___126_3180.FStar_Syntax_Syntax.lcomp_res_typ);
                         FStar_Syntax_Syntax.lcomp_cflags =
                           (uu___126_3180.FStar_Syntax_Syntax.lcomp_cflags);
                         FStar_Syntax_Syntax.lcomp_as_comp = bind_it
                       })))
  
let label :
  Prims.string ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        (FStar_Syntax_Syntax.mk
           (FStar_Syntax_Syntax.Tm_meta
              (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false)))))
          None f.FStar_Syntax_Syntax.pos
  
let label_opt :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) Prims.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | None  -> f
          | Some reason1 ->
              let uu____3224 =
                let uu____3225 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3225  in
              if uu____3224
              then f
              else (let uu____3227 = reason1 ()  in label uu____3227 r f)
  
let label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___127_3238 = g  in
            let uu____3239 =
              let uu____3240 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3240  in
            {
              FStar_TypeChecker_Env.guard_f = uu____3239;
              FStar_TypeChecker_Env.deferred =
                (uu___127_3238.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___127_3238.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___127_3238.FStar_TypeChecker_Env.implicits)
            }
  
let weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____3250 -> g2
  
let weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____3267 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          match f with
          | FStar_TypeChecker_Common.Trivial  -> c
          | FStar_TypeChecker_Common.NonTrivial f1 ->
              let uu____3274 = FStar_Syntax_Util.is_ml_comp c  in
              if uu____3274
              then c
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let wp =
                   let uu____3283 =
                     let uu____3284 =
                       FStar_All.pipe_right nct.FStar_TypeChecker_Env.nct_wp
                         Prims.fst
                        in
                     uu____3284.FStar_Syntax_Syntax.pos  in
                   let uu____3291 =
                     let uu____3292 =
                       FStar_TypeChecker_Env.inst_effect_fun_with
                         nct.FStar_TypeChecker_Env.nct_univs env md
                         md.FStar_Syntax_Syntax.assume_p
                        in
                     let uu____3293 =
                       let uu____3294 =
                         let uu____3300 =
                           let uu____3302 = FStar_Syntax_Syntax.as_arg f1  in
                           [uu____3302; nct.FStar_TypeChecker_Env.nct_wp]  in
                         (nct.FStar_TypeChecker_Env.nct_result) :: uu____3300
                          in
                       FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices uu____3294
                        in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3292 uu____3293  in
                   uu____3291 None uu____3283  in
                 let uu____3311 =
                   let uu___128_3312 = nct  in
                   let uu____3313 = FStar_Syntax_Syntax.as_arg wp  in
                   {
                     FStar_TypeChecker_Env.nct_name =
                       (uu___128_3312.FStar_TypeChecker_Env.nct_name);
                     FStar_TypeChecker_Env.nct_univs =
                       (uu___128_3312.FStar_TypeChecker_Env.nct_univs);
                     FStar_TypeChecker_Env.nct_indices =
                       (uu___128_3312.FStar_TypeChecker_Env.nct_indices);
                     FStar_TypeChecker_Env.nct_result =
                       (uu___128_3312.FStar_TypeChecker_Env.nct_result);
                     FStar_TypeChecker_Env.nct_wp = uu____3313;
                     FStar_TypeChecker_Env.nct_flags =
                       (uu___128_3312.FStar_TypeChecker_Env.nct_flags)
                   }  in
                 FStar_TypeChecker_Env.normal_comp_typ_as_comp env uu____3311)
           in
        let uu____3314 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____3314
        then lc
        else
          (let uu___129_3316 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___129_3316.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___129_3316.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___129_3316.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___129_3316.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___129_3316.FStar_Syntax_Syntax.lcomp_cflags);
             FStar_Syntax_Syntax.lcomp_as_comp = weaken
           })
  
let strengthen_precondition :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t)
  =
  fun reason  ->
    fun env  ->
      fun e  ->
        fun lc  ->
          fun g0  ->
            let uu____3343 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____3343
            then (lc, g0)
            else
              ((let uu____3348 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    FStar_Options.Extreme
                   in
                if uu____3348
                then
                  let uu____3349 =
                    FStar_TypeChecker_Normalize.term_to_string env e  in
                  let uu____3350 =
                    FStar_TypeChecker_Rel.guard_to_string env g0  in
                  FStar_Util.print2
                    "+++++++++++++Strengthening pre-condition of term %s with guard %s\n"
                    uu____3349 uu____3350
                else ());
               (let strengthen uu____3357 =
                  let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                  let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                  let uu____3362 = FStar_TypeChecker_Rel.guard_form g01  in
                  match uu____3362 with
                  | FStar_TypeChecker_Common.Trivial  -> c
                  | FStar_TypeChecker_Common.NonTrivial f ->
                      let c1 =
                        let uu____3369 =
                          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                            (let uu____3370 =
                               FStar_Syntax_Util.is_partial_return c  in
                             Prims.op_Negation uu____3370)
                           in
                        if uu____3369
                        then
                          let x =
                            let uu____3374 =
                              FStar_TypeChecker_Env.result_typ env c  in
                            FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                              None uu____3374
                             in
                          let xret =
                            let uu____3378 =
                              let uu____3379 =
                                FStar_Syntax_Syntax.bv_to_name x  in
                              return_value env x.FStar_Syntax_Syntax.sort
                                uu____3379
                               in
                            FStar_Syntax_Util.comp_set_flags uu____3378
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             in
                          let lc1 =
                            let uu____3381 =
                              FStar_TypeChecker_Env.lcomp_of_comp env c  in
                            let uu____3382 =
                              let uu____3383 =
                                FStar_TypeChecker_Env.lcomp_of_comp env xret
                                 in
                              ((Some x), uu____3383)  in
                            bind env (Some e) uu____3381 uu____3382  in
                          lc1.FStar_Syntax_Syntax.lcomp_as_comp ()
                        else c  in
                      ((let uu____3387 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Extreme
                           in
                        if uu____3387
                        then
                          let uu____3388 =
                            FStar_TypeChecker_Normalize.term_to_string env e
                             in
                          let uu____3389 =
                            FStar_TypeChecker_Normalize.term_to_string env f
                             in
                          FStar_Util.print2
                            "-------------Strengthening pre-condition of term %s with guard %s\n"
                            uu____3388 uu____3389
                        else ());
                       (let uu____3391 =
                          (FStar_Syntax_Util.is_tot_or_gtot_comp c1) ||
                            (FStar_Syntax_Util.is_named_tot_or_gtot_comp c1)
                           in
                        if uu____3391
                        then c1
                        else
                          (let nct =
                             FStar_TypeChecker_Env.comp_as_normal_comp_typ
                               env c1
                              in
                           let md =
                             FStar_TypeChecker_Env.get_effect_decl env
                               nct.FStar_TypeChecker_Env.nct_name
                              in
                           let wp =
                             let uu____3400 =
                               let uu____3401 =
                                 FStar_All.pipe_right
                                   nct.FStar_TypeChecker_Env.nct_wp Prims.fst
                                  in
                               uu____3401.FStar_Syntax_Syntax.pos  in
                             let uu____3408 =
                               let uu____3409 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   nct.FStar_TypeChecker_Env.nct_univs env md
                                   md.FStar_Syntax_Syntax.assert_p
                                  in
                               let uu____3410 =
                                 let uu____3411 =
                                   let uu____3417 =
                                     let uu____3419 =
                                       let uu____3420 =
                                         let uu____3421 =
                                           FStar_TypeChecker_Env.get_range
                                             env
                                            in
                                         label_opt env reason uu____3421 f
                                          in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____3420
                                        in
                                     [uu____3419;
                                     nct.FStar_TypeChecker_Env.nct_wp]  in
                                   (nct.FStar_TypeChecker_Env.nct_result) ::
                                     uu____3417
                                    in
                                 FStar_List.append
                                   nct.FStar_TypeChecker_Env.nct_indices
                                   uu____3411
                                  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____3409
                                 uu____3410
                                in
                             uu____3408 None uu____3400  in
                           (let uu____3431 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____3431
                            then
                              let uu____3432 =
                                FStar_Syntax_Print.term_to_string wp  in
                              FStar_Util.print1
                                "-------------Strengthened pre-condition is %s\n"
                                uu____3432
                            else ());
                           (let c2 =
                              let uu____3435 =
                                let uu___130_3436 = nct  in
                                let uu____3437 =
                                  FStar_Syntax_Syntax.as_arg wp  in
                                {
                                  FStar_TypeChecker_Env.nct_name =
                                    (uu___130_3436.FStar_TypeChecker_Env.nct_name);
                                  FStar_TypeChecker_Env.nct_univs =
                                    (uu___130_3436.FStar_TypeChecker_Env.nct_univs);
                                  FStar_TypeChecker_Env.nct_indices =
                                    (uu___130_3436.FStar_TypeChecker_Env.nct_indices);
                                  FStar_TypeChecker_Env.nct_result =
                                    (uu___130_3436.FStar_TypeChecker_Env.nct_result);
                                  FStar_TypeChecker_Env.nct_wp = uu____3437;
                                  FStar_TypeChecker_Env.nct_flags =
                                    (uu___130_3436.FStar_TypeChecker_Env.nct_flags)
                                }  in
                              FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                env uu____3435
                               in
                            c2))))
                   in
                let lc1 =
                  let flags =
                    let uu____3441 =
                      (FStar_Syntax_Util.is_pure_lcomp lc) &&
                        (let uu____3442 =
                           FStar_Syntax_Util.is_function_typ
                             lc.FStar_Syntax_Syntax.lcomp_res_typ
                            in
                         FStar_All.pipe_left Prims.op_Negation uu____3442)
                       in
                    if uu____3441
                    then
                      FStar_All.pipe_right
                        lc.FStar_Syntax_Syntax.lcomp_cflags
                        (FStar_List.collect
                           (fun uu___93_3446  ->
                              match uu___93_3446 with
                              | FStar_Syntax_Syntax.RETURN 
                                |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | uu____3448 -> []))
                    else []  in
                  let uu___131_3450 = lc  in
                  {
                    FStar_Syntax_Syntax.lcomp_name =
                      (uu___131_3450.FStar_Syntax_Syntax.lcomp_name);
                    FStar_Syntax_Syntax.lcomp_univs =
                      (uu___131_3450.FStar_Syntax_Syntax.lcomp_univs);
                    FStar_Syntax_Syntax.lcomp_indices =
                      (uu___131_3450.FStar_Syntax_Syntax.lcomp_indices);
                    FStar_Syntax_Syntax.lcomp_res_typ =
                      (uu___131_3450.FStar_Syntax_Syntax.lcomp_res_typ);
                    FStar_Syntax_Syntax.lcomp_cflags = flags;
                    FStar_Syntax_Syntax.lcomp_as_comp =
                      (uu___131_3450.FStar_Syntax_Syntax.lcomp_as_comp)
                  }  in
                let uu____3451 =
                  let uu____3452 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3452
                  then lc1
                  else
                    (let uu___132_3454 = lc1  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___132_3454.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___132_3454.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___132_3454.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ =
                         (uu___132_3454.FStar_Syntax_Syntax.lcomp_res_typ);
                       FStar_Syntax_Syntax.lcomp_cflags =
                         (uu___132_3454.FStar_Syntax_Syntax.lcomp_cflags);
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     })
                   in
                (uu____3451,
                  (let uu___133_3455 = g0  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___133_3455.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___133_3455.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___133_3455.FStar_TypeChecker_Env.implicits)
                   }))))
  
let add_equality_to_post_condition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun comp  ->
      fun res_t  ->
        let md_pure =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Syntax_Const.effect_PURE_lid
           in
        let x = FStar_Syntax_Syntax.new_bv None res_t  in
        let y = FStar_Syntax_Syntax.new_bv None res_t  in
        let uu____3470 =
          let uu____3473 = FStar_Syntax_Syntax.bv_to_name x  in
          let uu____3474 = FStar_Syntax_Syntax.bv_to_name y  in
          (uu____3473, uu____3474)  in
        match uu____3470 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t  in
            let yret =
              let uu____3483 =
                let uu____3484 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____3485 =
                  let uu____3486 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3487 =
                    let uu____3489 = FStar_Syntax_Syntax.as_arg yexp  in
                    [uu____3489]  in
                  uu____3486 :: uu____3487  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3484 uu____3485  in
              uu____3483 None res_t.FStar_Syntax_Syntax.pos  in
            let x_eq_y_yret =
              let uu____3497 =
                let uu____3498 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p
                   in
                let uu____3499 =
                  let uu____3500 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3501 =
                    let uu____3503 =
                      let uu____3504 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp  in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3504
                       in
                    let uu____3505 =
                      let uu____3507 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret
                         in
                      [uu____3507]  in
                    uu____3503 :: uu____3505  in
                  uu____3500 :: uu____3501  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3498 uu____3499  in
              uu____3497 None res_t.FStar_Syntax_Syntax.pos  in
            let forall_y_x_eq_y_yret =
              let uu____3515 =
                let uu____3516 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp
                   in
                let uu____3517 =
                  let uu____3518 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3519 =
                    let uu____3521 = FStar_Syntax_Syntax.as_arg res_t  in
                    let uu____3522 =
                      let uu____3524 =
                        let uu____3525 =
                          let uu____3526 =
                            let uu____3530 = FStar_Syntax_Syntax.mk_binder y
                               in
                            [uu____3530]  in
                          FStar_Syntax_Util.abs uu____3526 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL])))
                           in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3525
                         in
                      [uu____3524]  in
                    uu____3521 :: uu____3522  in
                  uu____3518 :: uu____3519  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3516 uu____3517  in
              uu____3515 None res_t.FStar_Syntax_Syntax.pos  in
            let lc2 =
              (mk_comp md_pure) [u_res_t] [] res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN]
               in
            let lc =
              let uu____3546 = FStar_TypeChecker_Env.lcomp_of_comp env comp
                 in
              let uu____3547 =
                let uu____3548 = FStar_TypeChecker_Env.lcomp_of_comp env lc2
                   in
                ((Some x), uu____3548)  in
              bind env None uu____3546 uu____3547  in
            lc.FStar_Syntax_Syntax.lcomp_as_comp ()
  
let fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____3556 =
        let uu____3557 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____3557  in
      FStar_Syntax_Syntax.fvar uu____3556 FStar_Syntax_Syntax.Delta_constant
        None
  
let bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.formula * FStar_Syntax_Syntax.lcomp) Prims.list ->
        FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let uu____3573 =
          let uu____3579 =
            let uu____3585 =
              let uu____3586 = FStar_Syntax_Syntax.mk_Total res_t  in
              FStar_TypeChecker_Env.lcomp_of_comp env uu____3586  in
            (uu____3585, [])  in
          FStar_List.fold_right
            (fun uu____3599  ->
               fun uu____3600  ->
                 match (uu____3599, uu____3600) with
                 | ((formula,lc),(out,lcases1)) ->
                     let uu____3637 = join_lcomp env lc out  in
                     (match uu____3637 with
                      | (lc1,_out) -> (lc1, ((formula, lc1) :: lcases1))))
            lcases uu____3579
           in
        match uu____3573 with
        | (lc,lcases1) ->
            let bind_cases uu____3665 =
              let if_then_else1 guard cthen celse =
                let uu____3676 = lift_and_destruct env cthen celse  in
                match uu____3676 with
                | (nct_then,nct_else) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        nct_then.FStar_TypeChecker_Env.nct_name
                       in
                    let wp =
                      let uu____3685 =
                        FStar_Range.union_ranges
                          (Prims.fst nct_then.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                          (Prims.fst nct_else.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                         in
                      let uu____3690 =
                        let uu____3691 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            nct_then.FStar_TypeChecker_Env.nct_univs env md
                            md.FStar_Syntax_Syntax.if_then_else
                           in
                        let uu____3692 =
                          let uu____3693 =
                            let uu____3699 = FStar_Syntax_Syntax.as_arg res_t
                               in
                            let uu____3700 =
                              let uu____3702 =
                                FStar_Syntax_Syntax.as_arg guard  in
                              [uu____3702;
                              nct_then.FStar_TypeChecker_Env.nct_wp;
                              nct_else.FStar_TypeChecker_Env.nct_wp]  in
                            uu____3699 :: uu____3700  in
                          FStar_List.append
                            nct_then.FStar_TypeChecker_Env.nct_indices
                            uu____3693
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3691 uu____3692
                         in
                      uu____3690 None uu____3685  in
                    (mk_comp md) nct_then.FStar_TypeChecker_Env.nct_univs
                      nct_then.FStar_TypeChecker_Env.nct_indices res_t wp []
                 in
              let default_case =
                let post_k =
                  let uu____3713 =
                    let uu____3714 = FStar_Syntax_Syntax.null_binder res_t
                       in
                    [uu____3714]  in
                  let uu____3715 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow uu____3713 uu____3715  in
                let kwp =
                  let uu____3717 =
                    let uu____3718 = FStar_Syntax_Syntax.null_binder post_k
                       in
                    [uu____3718]  in
                  let uu____3719 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow uu____3717 uu____3719  in
                let post = FStar_Syntax_Syntax.new_bv None post_k  in
                let wp =
                  let uu____3722 =
                    let uu____3726 = FStar_Syntax_Syntax.mk_binder post  in
                    [uu____3726]  in
                  let uu____3727 =
                    let uu____3728 =
                      let uu____3731 = FStar_TypeChecker_Env.get_range env
                         in
                      label FStar_TypeChecker_Err.exhaustiveness_check
                        uu____3731
                       in
                    let uu____3732 =
                      fvar_const env FStar_Syntax_Const.false_lid  in
                    FStar_All.pipe_left uu____3728 uu____3732  in
                  FStar_Syntax_Util.abs uu____3722 uu____3727
                    (Some
                       (FStar_Util.Inr
                          (FStar_Syntax_Const.effect_Tot_lid,
                            [FStar_Syntax_Syntax.TOTAL])))
                   in
                let md =
                  FStar_TypeChecker_Env.get_effect_decl env
                    FStar_Syntax_Const.effect_PURE_lid
                   in
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                (mk_comp md) [u_res_t] [] res_t wp []  in
              let comp =
                FStar_List.fold_right
                  (fun uu____3747  ->
                     fun celse  ->
                       match uu____3747 with
                       | (g,cthen) ->
                           let uu____3753 =
                             cthen.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                           if_then_else1 g uu____3753 celse) lcases1
                  default_case
                 in
              let uu____3754 =
                let uu____3755 = FStar_Options.split_cases ()  in
                uu____3755 > (Prims.parse_int "0")  in
              if uu____3754
              then add_equality_to_post_condition env comp res_t
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let share_post_wp =
                   let uu____3764 =
                     let uu____3765 =
                       FStar_TypeChecker_Env.inst_effect_fun_with
                         nct.FStar_TypeChecker_Env.nct_univs env md
                         md.FStar_Syntax_Syntax.ite_wp
                        in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3765
                       (FStar_List.append
                          nct.FStar_TypeChecker_Env.nct_indices
                          [nct.FStar_TypeChecker_Env.nct_result;
                          nct.FStar_TypeChecker_Env.nct_wp])
                      in
                   uu____3764 None
                     (Prims.fst nct.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                    in
                 (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
                   nct.FStar_TypeChecker_Env.nct_indices
                   (Prims.fst nct.FStar_TypeChecker_Env.nct_result)
                   share_post_wp [])
               in
            let uu____3778 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
            if uu____3778
            then lc
            else
              (let uu___134_3780 = lc  in
               {
                 FStar_Syntax_Syntax.lcomp_name =
                   (uu___134_3780.FStar_Syntax_Syntax.lcomp_name);
                 FStar_Syntax_Syntax.lcomp_univs =
                   (uu___134_3780.FStar_Syntax_Syntax.lcomp_univs);
                 FStar_Syntax_Syntax.lcomp_indices =
                   (uu___134_3780.FStar_Syntax_Syntax.lcomp_indices);
                 FStar_Syntax_Syntax.lcomp_res_typ =
                   (uu___134_3780.FStar_Syntax_Syntax.lcomp_res_typ);
                 FStar_Syntax_Syntax.lcomp_cflags =
                   (uu___134_3780.FStar_Syntax_Syntax.lcomp_cflags);
                 FStar_Syntax_Syntax.lcomp_as_comp = bind_cases
               })
  
let close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let close1 uu____3797 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3801 = FStar_Syntax_Util.is_ml_comp c  in
          if uu____3801
          then c
          else
            (let nct = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                in
             let md =
               FStar_TypeChecker_Env.get_effect_decl env
                 nct.FStar_TypeChecker_Env.nct_name
                in
             let r =
               (Prims.fst nct.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                in
             let closed_wp =
               FStar_List.fold_right
                 (fun x  ->
                    fun wp  ->
                      let us =
                        let uu____3817 =
                          let uu____3819 =
                            env.FStar_TypeChecker_Env.universe_of env
                              x.FStar_Syntax_Syntax.sort
                             in
                          [uu____3819]  in
                        FStar_List.append nct.FStar_TypeChecker_Env.nct_univs
                          uu____3817
                         in
                      let wp1 =
                        let uu____3821 =
                          let uu____3825 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3825]  in
                        FStar_Syntax_Util.abs uu____3821 wp
                          (Some
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])))
                         in
                      let uu____3835 =
                        let uu____3836 =
                          FStar_TypeChecker_Env.inst_effect_fun_with us env
                            md md.FStar_Syntax_Syntax.close_wp
                           in
                        let uu____3837 =
                          let uu____3838 =
                            let uu____3844 =
                              let uu____3846 =
                                FStar_Syntax_Syntax.as_arg
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____3847 =
                                let uu____3849 =
                                  FStar_Syntax_Syntax.as_arg wp1  in
                                [uu____3849]  in
                              uu____3846 :: uu____3847  in
                            (nct.FStar_TypeChecker_Env.nct_result) ::
                              uu____3844
                             in
                          FStar_List.append
                            nct.FStar_TypeChecker_Env.nct_indices uu____3838
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3836 uu____3837
                         in
                      uu____3835 None r) bvs
                 (Prims.fst nct.FStar_TypeChecker_Env.nct_wp)
                in
             (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
               nct.FStar_TypeChecker_Env.nct_indices
               (Prims.fst nct.FStar_TypeChecker_Env.nct_result) closed_wp
               nct.FStar_TypeChecker_Env.nct_flags)
           in
        let uu____3862 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____3862
        then lc
        else
          (let uu___135_3864 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___135_3864.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___135_3864.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___135_3864.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___135_3864.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___135_3864.FStar_Syntax_Syntax.lcomp_cflags);
             FStar_Syntax_Syntax.lcomp_as_comp = close1
           })
  
let maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let refine1 uu____3879 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3883 =
            (let uu____3884 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.lcomp_name
                in
             Prims.op_Negation uu____3884) || env.FStar_TypeChecker_Env.lax
             in
          if uu____3883
          then c
          else
            (let uu____3888 = FStar_Syntax_Util.is_partial_return c  in
             if uu____3888
             then c
             else
               (let uu____3892 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (let uu____3893 =
                       FStar_TypeChecker_Env.lid_exists env
                         FStar_Syntax_Const.effect_GTot_lid
                        in
                     Prims.op_Negation uu____3893)
                   in
                if uu____3892
                then
                  let uu____3896 =
                    let uu____3897 =
                      FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                       in
                    let uu____3898 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format2 "%s: %s\n" uu____3897 uu____3898  in
                  failwith uu____3896
                else
                  (let nct =
                     FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
                   let t = Prims.fst nct.FStar_TypeChecker_Env.nct_result  in
                   let c1 =
                     FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (Some (t.FStar_Syntax_Syntax.pos)) t
                      in
                   let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                   let ret1 =
                     let uu____3912 =
                       let uu____3913 = return_value env t xexp  in
                       FStar_Syntax_Util.comp_set_flags uu____3913
                         [FStar_Syntax_Syntax.PARTIAL_RETURN]
                        in
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.lcomp_of_comp env) uu____3912
                      in
                   let eq1 =
                     let uu____3915 =
                       env.FStar_TypeChecker_Env.universe_of env t  in
                     FStar_Syntax_Util.mk_eq2 uu____3915 t xexp e  in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1)
                      in
                   let bind_lc =
                     let uu____3918 =
                       FStar_TypeChecker_Env.lcomp_of_comp env c1  in
                     bind env None uu____3918 ((Some x), eq_ret)  in
                   let uu____3920 =
                     bind_lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                   FStar_Syntax_Util.comp_set_flags uu____3920
                     (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                     (FStar_Syntax_Util.comp_flags c1)))))
           in
        let flags =
          let uu____3923 =
            ((let uu____3924 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              Prims.op_Negation uu____3924) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3925 = FStar_Syntax_Util.is_lcomp_partial_return lc
                  in
               Prims.op_Negation uu____3925)
             in
          if uu____3923
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.lcomp_cflags)
          else lc.FStar_Syntax_Syntax.lcomp_cflags  in
        let uu___136_3928 = lc  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (uu___136_3928.FStar_Syntax_Syntax.lcomp_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (uu___136_3928.FStar_Syntax_Syntax.lcomp_univs);
          FStar_Syntax_Syntax.lcomp_indices =
            (uu___136_3928.FStar_Syntax_Syntax.lcomp_indices);
          FStar_Syntax_Syntax.lcomp_res_typ =
            (uu___136_3928.FStar_Syntax_Syntax.lcomp_res_typ);
          FStar_Syntax_Syntax.lcomp_cflags = flags;
          FStar_Syntax_Syntax.lcomp_as_comp = refine1
        }
  
let check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____3947 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____3947 with
          | None  ->
              let uu____3952 =
                let uu____3953 =
                  let uu____3956 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c'
                     in
                  let uu____3957 = FStar_TypeChecker_Env.get_range env  in
                  (uu____3956, uu____3957)  in
                FStar_Errors.Error uu____3953  in
              Prims.raise uu____3952
          | Some g -> (e, c', g)
  
let maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let uu____3978 =
            let uu____3979 = FStar_Syntax_Subst.compress t  in
            uu____3979.FStar_Syntax_Syntax.n  in
          match uu____3978 with
          | FStar_Syntax_Syntax.Tm_type uu____3984 ->
              let uu____3985 =
                let uu____3986 =
                  FStar_Syntax_Subst.compress
                    lc.FStar_Syntax_Syntax.lcomp_res_typ
                   in
                uu____3986.FStar_Syntax_Syntax.n  in
              (match uu____3985 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____3992 =
                     FStar_TypeChecker_Env.lookup_lid env
                       FStar_Syntax_Const.b2t_lid
                      in
                   let b2t1 =
                     FStar_Syntax_Syntax.fvar
                       (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid
                          e.FStar_Syntax_Syntax.pos)
                       (FStar_Syntax_Syntax.Delta_defined_at_level
                          (Prims.parse_int "1")) None
                      in
                   let lc1 =
                     let uu____3997 =
                       let uu____3998 =
                         let uu____3999 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0
                            in
                         FStar_TypeChecker_Env.lcomp_of_comp env uu____3999
                          in
                       (None, uu____3998)  in
                     bind env (Some e) lc uu____3997  in
                   let e1 =
                     let uu____4004 =
                       let uu____4005 =
                         let uu____4006 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____4006]  in
                       FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4005  in
                     uu____4004
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   (e1, lc1)
               | uu____4013 -> (e, lc))
          | uu____4014 -> (e, lc)
  
let weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp *
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let gopt =
            if env.FStar_TypeChecker_Env.use_eq
            then
              let uu____4040 =
                FStar_TypeChecker_Rel.try_teq env
                  lc.FStar_Syntax_Syntax.lcomp_res_typ t
                 in
              (uu____4040, false)
            else
              (let uu____4044 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.lcomp_res_typ t
                  in
               (uu____4044, true))
             in
          match gopt with
          | (None ,uu____4050) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.lcomp_res_typ t;
               (e,
                 ((let uu___137_4053 = lc  in
                   {
                     FStar_Syntax_Syntax.lcomp_name =
                       (uu___137_4053.FStar_Syntax_Syntax.lcomp_name);
                     FStar_Syntax_Syntax.lcomp_univs =
                       (uu___137_4053.FStar_Syntax_Syntax.lcomp_univs);
                     FStar_Syntax_Syntax.lcomp_indices =
                       (uu___137_4053.FStar_Syntax_Syntax.lcomp_indices);
                     FStar_Syntax_Syntax.lcomp_res_typ = t;
                     FStar_Syntax_Syntax.lcomp_cflags =
                       (uu___137_4053.FStar_Syntax_Syntax.lcomp_cflags);
                     FStar_Syntax_Syntax.lcomp_as_comp =
                       (uu___137_4053.FStar_Syntax_Syntax.lcomp_as_comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4057 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____4057 with
               | FStar_TypeChecker_Common.Trivial  ->
                   (e,
                     (let uu___138_4061 = lc  in
                      {
                        FStar_Syntax_Syntax.lcomp_name =
                          (uu___138_4061.FStar_Syntax_Syntax.lcomp_name);
                        FStar_Syntax_Syntax.lcomp_univs =
                          (uu___138_4061.FStar_Syntax_Syntax.lcomp_univs);
                        FStar_Syntax_Syntax.lcomp_indices =
                          (uu___138_4061.FStar_Syntax_Syntax.lcomp_indices);
                        FStar_Syntax_Syntax.lcomp_res_typ = t;
                        FStar_Syntax_Syntax.lcomp_cflags =
                          (uu___138_4061.FStar_Syntax_Syntax.lcomp_cflags);
                        FStar_Syntax_Syntax.lcomp_as_comp =
                          (uu___138_4061.FStar_Syntax_Syntax.lcomp_as_comp)
                      }), g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4064 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4064.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4064.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4064.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____4070 =
                     let uu____4071 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____4071
                     then lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f
                           in
                        let uu____4076 =
                          let uu____4077 = FStar_Syntax_Subst.compress f1  in
                          uu____4077.FStar_Syntax_Syntax.n  in
                        match uu____4076 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4082,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4084;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4085;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4086;_},uu____4087)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4111 = lc  in
                              {
                                FStar_Syntax_Syntax.lcomp_name =
                                  (uu___140_4111.FStar_Syntax_Syntax.lcomp_name);
                                FStar_Syntax_Syntax.lcomp_univs =
                                  (uu___140_4111.FStar_Syntax_Syntax.lcomp_univs);
                                FStar_Syntax_Syntax.lcomp_indices =
                                  (uu___140_4111.FStar_Syntax_Syntax.lcomp_indices);
                                FStar_Syntax_Syntax.lcomp_res_typ = t;
                                FStar_Syntax_Syntax.lcomp_cflags =
                                  (uu___140_4111.FStar_Syntax_Syntax.lcomp_cflags);
                                FStar_Syntax_Syntax.lcomp_as_comp =
                                  (uu___140_4111.FStar_Syntax_Syntax.lcomp_as_comp)
                              }  in
                            lc1.FStar_Syntax_Syntax.lcomp_as_comp ()
                        | uu____4112 ->
                            let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                               in
                            ((let uu____4117 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4117
                              then
                                let uu____4118 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.lcomp_res_typ
                                   in
                                let uu____4119 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____4120 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____4121 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4118 uu____4119 uu____4120 uu____4121
                              else ());
                             (let nct =
                                FStar_TypeChecker_Env.comp_as_normal_comp_typ
                                  env c
                                 in
                              let md =
                                FStar_TypeChecker_Env.get_effect_decl env
                                  nct.FStar_TypeChecker_Env.nct_name
                                 in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (Some (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let wp =
                                let uu____4130 =
                                  let uu____4131 =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      nct.FStar_TypeChecker_Env.nct_univs env
                                      md md.FStar_Syntax_Syntax.ret_wp
                                     in
                                  let uu____4132 =
                                    let uu____4133 =
                                      let uu____4139 =
                                        FStar_Syntax_Syntax.as_arg t  in
                                      let uu____4140 =
                                        let uu____4142 =
                                          FStar_Syntax_Syntax.as_arg xexp  in
                                        [uu____4142]  in
                                      uu____4139 :: uu____4140  in
                                    FStar_List.append
                                      nct.FStar_TypeChecker_Env.nct_indices
                                      uu____4133
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____4131
                                    uu____4132
                                   in
                                uu____4130 None xexp.FStar_Syntax_Syntax.pos
                                 in
                              let cret =
                                let uu____4152 =
                                  (mk_comp md)
                                    nct.FStar_TypeChecker_Env.nct_univs
                                    nct.FStar_TypeChecker_Env.nct_indices t
                                    wp [FStar_Syntax_Syntax.RETURN]
                                   in
                                FStar_TypeChecker_Env.lcomp_of_comp env
                                  uu____4152
                                 in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____4158 =
                                    let uu____4159 =
                                      let uu____4160 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____4160]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____4159
                                     in
                                  uu____4158
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____4166 =
                                let uu____4169 =
                                  FStar_All.pipe_left
                                    (fun _0_28  -> Some _0_28)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env
                                       lc.FStar_Syntax_Syntax.lcomp_res_typ t)
                                   in
                                let uu____4180 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____4181 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____4169 uu____4180
                                  e cret uu____4181
                                 in
                              match uu____4166 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___141_4187 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___141_4187.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___141_4187.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.lcomp_res_typ)
                                    }  in
                                  let c1 =
                                    let uu____4189 =
                                      let uu____4190 =
                                        FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                          env nct
                                         in
                                      FStar_TypeChecker_Env.lcomp_of_comp env
                                        uu____4190
                                       in
                                    bind env (Some e) uu____4189
                                      ((Some x1), eq_ret)
                                     in
                                  let c2 =
                                    c1.FStar_Syntax_Syntax.lcomp_as_comp ()
                                     in
                                  ((let uu____4196 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____4196
                                    then
                                      let uu____4197 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____4197
                                    else ());
                                   c2))))
                      in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                       (FStar_List.collect
                          (fun uu___94_4203  ->
                             match uu___94_4203 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4205 -> []))
                      in
                   let lc1 =
                     let uu___142_4207 = lc  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___142_4207.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___142_4207.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___142_4207.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ = t;
                       FStar_Syntax_Syntax.lcomp_cflags = flags;
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     }  in
                   let g2 =
                     let uu___143_4209 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4209.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4209.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4209.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
let pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv None res_t  in
        let uu____4229 =
          let uu____4230 =
            let uu____4231 =
              let uu____4232 =
                let uu____4233 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____4233  in
              [uu____4232]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4231  in
          uu____4230 None res_t.FStar_Syntax_Syntax.pos  in
        FStar_Syntax_Util.refine x uu____4229  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____4242 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____4242
      then
        let uu____4246 = FStar_TypeChecker_Env.result_typ env comp  in
        (None, uu____4246)
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal _|FStar_Syntax_Syntax.Total _ ->
             failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                  FStar_Syntax_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                    FStar_Syntax_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (res,uu____4265)::(req,uu____4267)::(ens,uu____4269)::uu____4270
                    ->
                    let uu____4300 =
                      let uu____4302 = norm req  in Some uu____4302  in
                    let uu____4303 =
                      let uu____4304 = mk_post_type res ens  in
                      FStar_All.pipe_left norm uu____4304  in
                    (uu____4300, uu____4303)
                | uu____4306 ->
                    let uu____4312 =
                      let uu____4313 =
                        let uu____4316 =
                          let uu____4317 =
                            FStar_Syntax_Print.comp_to_string comp  in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4317
                           in
                        (uu____4316, (comp.FStar_Syntax_Syntax.pos))  in
                      FStar_Errors.Error uu____4313  in
                    Prims.raise uu____4312)
             else
               (let nct =
                  FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                let res_t = Prims.fst nct.FStar_TypeChecker_Env.nct_result
                   in
                let wp = Prims.fst nct.FStar_TypeChecker_Env.nct_wp  in
                let uu____4333 =
                  FStar_TypeChecker_Env.lookup_lid env
                    FStar_Syntax_Const.as_requires
                   in
                match uu____4333 with
                | (us_r,uu____4340) ->
                    let uu____4341 =
                      FStar_TypeChecker_Env.lookup_lid env
                        FStar_Syntax_Const.as_ensures
                       in
                    (match uu____4341 with
                     | (us_e,uu____4348) ->
                         let r = res_t.FStar_Syntax_Syntax.pos  in
                         let as_req =
                           let uu____4351 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_requires r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst uu____4351 us_r
                            in
                         let as_ens =
                           let uu____4353 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_ensures r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst uu____4353 us_e
                            in
                         let req =
                           let uu____4357 =
                             let uu____4358 =
                               let uu____4359 =
                                 let uu____4366 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____4366]  in
                               (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                 uu____4359
                                in
                             FStar_Syntax_Syntax.mk_Tm_app as_req uu____4358
                              in
                           uu____4357
                             (Some
                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                             r
                            in
                         let ens =
                           let uu____4382 =
                             let uu____4383 =
                               let uu____4384 =
                                 let uu____4391 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____4391]  in
                               (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                 uu____4384
                                in
                             FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4383
                              in
                           uu____4382 None r  in
                         let uu____4404 =
                           let uu____4406 = norm req  in Some uu____4406  in
                         let uu____4407 =
                           let uu____4408 = mk_post_type res_t ens  in
                           norm uu____4408  in
                         (uu____4404, uu____4407))))
  
let maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.subst_t)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard, [])
        else
          (let number_of_implicits t1 =
             let uu____4438 = FStar_Syntax_Util.arrow_formals_comp t1  in
             match uu____4438 with
             | (formals,uu____4445) ->
                 let n_implicits =
                   let uu____4453 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4490  ->
                             match uu____4490 with
                             | (uu____4494,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____4453 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____4566 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____4566 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____4580 =
                     let uu____4581 =
                       let uu____4584 =
                         let uu____4585 = FStar_Util.string_of_int n_expected
                            in
                         let uu____4589 = FStar_Syntax_Print.term_to_string e
                            in
                         let uu____4590 =
                           FStar_Util.string_of_int n_available  in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4585 uu____4589 uu____4590
                          in
                       let uu____4594 = FStar_TypeChecker_Env.get_range env
                          in
                       (uu____4584, uu____4594)  in
                     FStar_Errors.Error uu____4581  in
                   Prims.raise uu____4580
                 else Some (n_available - n_expected)
              in
           let decr_inst uu___95_4607 =
             match uu___95_4607 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1"))  in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4627 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____4627 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_29,uu____4689) when
                          _0_29 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4711,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____4730 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____4730 with
                           | (v1,uu____4751,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____4761 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____4761 with
                                | (args,bs3,subst3,g') ->
                                    let uu____4810 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____4810)))
                      | (uu____4824,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____4848 =
                      let uu____4862 = inst_n_binders t  in
                      aux [] uu____4862 bs1  in
                    (match uu____4848 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____4902) -> (e, torig, guard, [])
                          | (uu____4919,[]) when
                              let uu____4935 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____4935 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard,
                                [])
                          | uu____4937 ->
                              let t1 =
                                match bs2 with
                                | [] ->
                                    FStar_TypeChecker_Env.result_typ env c1
                                | uu____4952 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard, subst1))))
           | uu____4968 -> (e, t, FStar_TypeChecker_Rel.trivial_guard, []))
  
let string_of_univs univs1 =
  let uu____4981 =
    let uu____4983 = FStar_Util.set_elements univs1  in
    FStar_All.pipe_right uu____4983
      (FStar_List.map
         (fun u  ->
            let uu____4993 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____4993 FStar_Util.string_of_int))
     in
  FStar_All.pipe_right uu____4981 (FStar_String.concat ", ") 
let gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5005 = FStar_Util.set_is_empty x  in
      if uu____5005
      then []
      else
        (let s =
           let uu____5010 =
             let uu____5012 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____5012  in
           FStar_All.pipe_right uu____5010 FStar_Util.set_elements  in
         (let uu____5017 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____5017
          then
            let uu____5018 =
              let uu____5019 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____5019  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5018
          else ());
         (let r =
            let uu____5027 = FStar_TypeChecker_Env.get_range env  in
            Some uu____5027  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____5039 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____5039
                     then
                       let uu____5040 =
                         let uu____5041 = FStar_Unionfind.uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5041
                          in
                       let uu____5043 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____5044 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5040 uu____5043 uu____5044
                     else ());
                    FStar_Unionfind.change u
                      (Some (FStar_Syntax_Syntax.U_name u_name));
                    u_name))
             in
          u_names))
  
let gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____5061 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____5061 FStar_Util.fifo_set_elements  in
      univnames1
  
let maybe_set_tk ts uu___96_5088 =
  match uu___96_5088 with
  | None  -> ts
  | Some t ->
      let t1 = FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange  in
      let t2 = FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t1  in
      (FStar_ST.write (Prims.snd ts).FStar_Syntax_Syntax.tk
         (Some (t2.FStar_Syntax_Syntax.n));
       ts)
  
let check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____5129) -> generalized_univ_names
        | (uu____5133,[]) -> explicit_univ_names
        | uu____5137 ->
            let uu____5142 =
              let uu____5143 =
                let uu____5146 =
                  let uu____5147 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5147
                   in
                (uu____5146, (t.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____5143  in
            Prims.raise uu____5142
  
let generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      let univs1 = FStar_Syntax_Free.univs t  in
      (let uu____5160 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____5160
       then
         let uu____5161 = string_of_univs univs1  in
         FStar_Util.print1 "univs to gen : %s\n" uu____5161
       else ());
      (let gen1 = gen_univs env univs1  in
       (let uu____5167 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____5167
        then
          let uu____5168 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.print1 "After generalization: %s\n" uu____5168
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0  in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t  in
        let uu____5173 = FStar_ST.read t0.FStar_Syntax_Syntax.tk  in
        maybe_set_tk (univs2, ts) uu____5173))
  
let gen :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5203 =
        let uu____5204 =
          FStar_Util.for_all
            (fun uu____5209  ->
               match uu____5209 with
               | (uu____5214,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs
           in
        FStar_All.pipe_left Prims.op_Negation uu____5204  in
      if uu____5203
      then None
      else
        (let norm c =
           (let uu____5237 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____5237
            then
              let uu____5238 = FStar_Syntax_Print.comp_to_string c  in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5238
            else ());
           (let c1 =
              let uu____5241 = FStar_TypeChecker_Env.should_verify env  in
              if uu____5241
              then
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Eager_unfolding;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
              else
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.NoFullNorm] env c
               in
            (let uu____5244 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____5244
             then
               let uu____5245 = FStar_Syntax_Print.comp_to_string c1  in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5245
             else ());
            c1)
            in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
         let gen_uvars uvs =
           let uu____5279 = FStar_Util.set_difference uvs env_uvars  in
           FStar_All.pipe_right uu____5279 FStar_Util.set_elements  in
         let uu____5323 =
           let uu____5341 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5394  ->
                     match uu____5394 with
                     | (e,c) ->
                         let c1 = norm c  in
                         let t =
                           let uu____5416 =
                             FStar_TypeChecker_Env.result_typ env c1  in
                           FStar_All.pipe_right uu____5416
                             FStar_Syntax_Subst.compress
                            in
                         let univs1 = FStar_Syntax_Free.univs t  in
                         let uvt = FStar_Syntax_Free.uvars t  in
                         let uvs = gen_uvars uvt  in (univs1, (uvs, e, c1))))
              in
           FStar_All.pipe_right uu____5341 FStar_List.unzip  in
         match uu____5323 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1
                in
             let gen_univs1 = gen_univs env univs2  in
             ((let uu____5546 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____5546
               then
                 FStar_All.pipe_right gen_univs1
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.print1 "Generalizing uvar %s\n"
                           x.FStar_Ident.idText))
               else ());
              (let ecs1 =
                 FStar_All.pipe_right uvars1
                   (FStar_List.map
                      (fun uu____5588  ->
                         match uu____5588 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5645  ->
                                       match uu____5645 with
                                       | (u,k) ->
                                           let uu____5665 =
                                             FStar_Unionfind.find u  in
                                           (match uu____5665 with
                                            | FStar_Syntax_Syntax.Fixed
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_name
                                                  a;
                                                FStar_Syntax_Syntax.tk = _;
                                                FStar_Syntax_Syntax.pos = _;
                                                FStar_Syntax_Syntax.vars = _;_}
                                              |FStar_Syntax_Syntax.Fixed
                                              {
                                                FStar_Syntax_Syntax.n =
                                                  FStar_Syntax_Syntax.Tm_abs
                                                  (_,{
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_name
                                                         a;
                                                       FStar_Syntax_Syntax.tk
                                                         = _;
                                                       FStar_Syntax_Syntax.pos
                                                         = _;
                                                       FStar_Syntax_Syntax.vars
                                                         = _;_},_);
                                                FStar_Syntax_Syntax.tk = _;
                                                FStar_Syntax_Syntax.pos = _;
                                                FStar_Syntax_Syntax.vars = _;_}
                                                ->
                                                (a,
                                                  (Some
                                                     FStar_Syntax_Syntax.imp_tag))
                                            | FStar_Syntax_Syntax.Fixed
                                                uu____5703 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5711 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k
                                                   in
                                                let uu____5716 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    k1
                                                   in
                                                (match uu____5716 with
                                                 | (bs,cres) ->
                                                     let kres =
                                                       FStar_TypeChecker_Env.result_typ
                                                         env cres
                                                        in
                                                     let a =
                                                       let uu____5735 =
                                                         let uu____5737 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _0_30  ->
                                                              Some _0_30)
                                                           uu____5737
                                                          in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____5735 kres
                                                        in
                                                     let t =
                                                       let uu____5740 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       let uu____5741 =
                                                         let uu____5748 =
                                                           let uu____5754 =
                                                             let uu____5755 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres
                                                                in
                                                             FStar_TypeChecker_Env.lcomp_of_comp
                                                               env uu____5755
                                                              in
                                                           FStar_Util.Inl
                                                             uu____5754
                                                            in
                                                         Some uu____5748  in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____5740
                                                         uu____5741
                                                        in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag)))))))
                                in
                             let uu____5768 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | ([],uu____5786) ->
                                   let c1 =
                                     FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env c
                                      in
                                   let e1 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta;
                                       FStar_TypeChecker_Normalize.NoDeltaSteps;
                                       FStar_TypeChecker_Normalize.NoFullNorm]
                                       env e
                                      in
                                   (e1, c1)
                               | uu____5798 ->
                                   let uu____5806 = (e, c)  in
                                   (match uu____5806 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Iota;
                                            FStar_TypeChecker_Normalize.NoFullNorm]
                                            env e
                                           in
                                        let t =
                                          let uu____5816 =
                                            let uu____5817 =
                                              let uu____5820 =
                                                FStar_TypeChecker_Env.result_typ
                                                  env c1
                                                 in
                                              FStar_Syntax_Subst.compress
                                                uu____5820
                                               in
                                            uu____5817.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5816 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____5833 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____5833 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____5841 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1
                                           in
                                        let e' =
                                          let uu____5843 =
                                            let uu____5850 =
                                              let uu____5856 =
                                                FStar_TypeChecker_Env.lcomp_of_comp
                                                  env c1
                                                 in
                                              FStar_Util.Inl uu____5856  in
                                            Some uu____5850  in
                                          FStar_Syntax_Util.abs tvars e1
                                            uu____5843
                                           in
                                        let uu____5865 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____5865))
                                in
                             (match uu____5768 with
                              | (e1,c1) -> (gen_univs1, e1, c1))))
                  in
               Some ecs1)))
  
let generalize :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name Prims.list
        * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list
  =
  fun env  ->
    fun lecs  ->
      (let uu____5903 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____5903
       then
         let uu____5904 =
           let uu____5905 =
             FStar_List.map
               (fun uu____5910  ->
                  match uu____5910 with
                  | (lb,uu____5915,uu____5916) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs
              in
           FStar_All.pipe_right uu____5905 (FStar_String.concat ", ")  in
         FStar_Util.print1 "Generalizing: %s\n" uu____5904
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____5924  ->
              match uu____5924 with | (l,t,c) -> gather_free_univnames env t)
           lecs
          in
       let generalized_lecs =
         let uu____5938 =
           let uu____5945 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5961  ->
                     match uu____5961 with | (uu____5967,e,c) -> (e, c)))
              in
           gen env uu____5945  in
         match uu____5938 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5999  ->
                     match uu____5999 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6039  ->
                  fun uu____6040  ->
                    match (uu____6039, uu____6040) with
                    | ((l,uu____6067,uu____6068),(us,e,c)) ->
                        ((let uu____6088 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium
                             in
                          if uu____6088
                          then
                            let uu____6089 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____6090 =
                              FStar_Syntax_Print.lbname_to_string l  in
                            let uu____6091 =
                              let uu____6092 =
                                FStar_TypeChecker_Env.result_typ env c  in
                              FStar_Syntax_Print.term_to_string uu____6092
                               in
                            let uu____6093 =
                              FStar_Syntax_Print.term_to_string e  in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6089 uu____6090 uu____6091 uu____6093
                          else ());
                         (l, us, e, c))) lecs ecs
          in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6110  ->
              match uu____6110 with
              | (l,generalized_univs,t,c) ->
                  let uu____6128 =
                    check_universe_generalization univnames1
                      generalized_univs t
                     in
                  (l, uu____6128, t, c)) univnames_lecs generalized_lecs)
  
let check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq env2 t11 t21
            else
              (let uu____6161 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21  in
               match uu____6161 with
               | None  -> None
               | Some f ->
                   let uu____6165 = FStar_TypeChecker_Rel.apply_guard f e  in
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____6165)
             in
          let is_var e1 =
            let uu____6171 =
              let uu____6172 = FStar_Syntax_Subst.compress e1  in
              uu____6172.FStar_Syntax_Syntax.n  in
            match uu____6171 with
            | FStar_Syntax_Syntax.Tm_name uu____6175 -> true
            | uu____6176 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___144_6198 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___144_6198.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___144_6198.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6199 ->
                let uu___145_6200 = e2  in
                let uu____6201 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n))  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6200.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6201;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6200.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6200.FStar_Syntax_Syntax.vars)
                }
             in
          let env2 =
            let uu___146_6210 = env1  in
            let uu____6211 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6210.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6210.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6210.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6210.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6210.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6210.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6210.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6210.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6210.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6210.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6210.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6210.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6210.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6210.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6210.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6211;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6210.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6210.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6210.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6210.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6210.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6210.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6210.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6210.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____6212 = check env2 t1 t2  in
          match uu____6212 with
          | None  ->
              let uu____6216 =
                let uu____6217 =
                  let uu____6220 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1
                     in
                  let uu____6221 = FStar_TypeChecker_Env.get_range env2  in
                  (uu____6220, uu____6221)  in
                FStar_Errors.Error uu____6217  in
              Prims.raise uu____6216
          | Some g ->
              ((let uu____6226 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____6226
                then
                  let uu____6227 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6227
                else ());
               (let uu____6229 = decorate e t2  in (uu____6229, g)))
  
let check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp -> (Prims.bool * FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____6253 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____6253
        then
          let uu____6256 = discharge g1  in
          let uu____6257 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          (uu____6256, uu____6257)
        else
          (let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
           let steps = [FStar_TypeChecker_Normalize.Beta]  in
           let c1 =
             let uu____6269 =
               let uu____6270 =
                 let uu____6271 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____6271 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____6270
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____6269
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let nct =
             let uu____6273 = FStar_Syntax_Syntax.mk_Comp c1  in
             FStar_TypeChecker_Env.comp_as_normal_comp_typ env uu____6273  in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               nct.FStar_TypeChecker_Env.nct_name
              in
           let vc =
             let uu____6278 = FStar_TypeChecker_Env.get_range env  in
             let uu____6279 =
               let uu____6280 =
                 FStar_TypeChecker_Env.inst_effect_fun_with
                   nct.FStar_TypeChecker_Env.nct_univs env md
                   md.FStar_Syntax_Syntax.trivial
                  in
               FStar_Syntax_Syntax.mk_Tm_app uu____6280
                 (FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                    [nct.FStar_TypeChecker_Env.nct_result;
                    nct.FStar_TypeChecker_Env.nct_wp])
                in
             uu____6279
               (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
               uu____6278
              in
           (let uu____6290 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____6290
            then
              let uu____6291 = FStar_Syntax_Print.term_to_string vc  in
              FStar_Util.print1 "top-level VC: %s\n" uu____6291
            else ());
           (let g2 =
              let uu____6294 =
                FStar_All.pipe_left
                  FStar_TypeChecker_Rel.guard_of_guard_formula
                  (FStar_TypeChecker_Common.NonTrivial vc)
                 in
              FStar_TypeChecker_Rel.conj_guard g1 uu____6294  in
            let uu____6295 = discharge g2  in
            let uu____6296 = FStar_Syntax_Syntax.mk_Comp c1  in
            (uu____6295, uu____6296)))
  
let short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___97_6320 =
        match uu___97_6320 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6326)::[] -> f fst1
        | uu____6339 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____6344 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____6344
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32)
         in
      let op_or_e e =
        let uu____6353 =
          let uu____6356 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____6356  in
        FStar_All.pipe_right uu____6353
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34)
         in
      let op_or_t t =
        let uu____6367 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____6367
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36)
         in
      let short_op_ite uu___98_6381 =
        match uu___98_6381 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6387)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6402)::[] ->
            let uu____6423 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____6423
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6428 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____6435 =
          let uu____6440 = short_bin_op op_and_e  in
          (FStar_Syntax_Const.op_And, uu____6440)  in
        let uu____6445 =
          let uu____6451 =
            let uu____6456 = short_bin_op op_or_e  in
            (FStar_Syntax_Const.op_Or, uu____6456)  in
          let uu____6461 =
            let uu____6467 =
              let uu____6472 = short_bin_op op_and_t  in
              (FStar_Syntax_Const.and_lid, uu____6472)  in
            let uu____6477 =
              let uu____6483 =
                let uu____6488 = short_bin_op op_or_t  in
                (FStar_Syntax_Const.or_lid, uu____6488)  in
              let uu____6493 =
                let uu____6499 =
                  let uu____6504 = short_bin_op op_imp_t  in
                  (FStar_Syntax_Const.imp_lid, uu____6504)  in
                [uu____6499; (FStar_Syntax_Const.ite_lid, short_op_ite)]  in
              uu____6483 :: uu____6493  in
            uu____6467 :: uu____6477  in
          uu____6451 :: uu____6461  in
        uu____6435 :: uu____6445  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____6545 =
            FStar_Util.find_map table
              (fun uu____6551  ->
                 match uu____6551 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6564 = mk1 seen_args  in Some uu____6564
                     else None)
             in
          (match uu____6545 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6567 -> FStar_TypeChecker_Common.Trivial
  
let short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6571 =
      let uu____6572 = FStar_Syntax_Util.un_uinst l  in
      uu____6572.FStar_Syntax_Syntax.n  in
    match uu____6571 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6576 -> false
  
let maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6594)::uu____6595 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6601 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____6605,Some (FStar_Syntax_Syntax.Implicit uu____6606))::uu____6607
          -> bs
      | uu____6616 ->
          let uu____6617 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____6617 with
           | None  -> bs
           | Some t ->
               let uu____6620 =
                 let uu____6621 = FStar_Syntax_Subst.compress t  in
                 uu____6621.FStar_Syntax_Syntax.n  in
               (match uu____6620 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6625) ->
                    let uu____6636 =
                      FStar_Util.prefix_until
                        (fun uu___99_6655  ->
                           match uu___99_6655 with
                           | (uu____6659,Some (FStar_Syntax_Syntax.Implicit
                              uu____6660)) -> false
                           | uu____6662 -> true) bs'
                       in
                    (match uu____6636 with
                     | None  -> bs
                     | Some ([],uu____6680,uu____6681) -> bs
                     | Some (imps,uu____6718,uu____6719) ->
                         let uu____6756 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____6764  ->
                                   match uu____6764 with
                                   | (x,uu____6769) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____6756
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____6792  ->
                                     match uu____6792 with
                                     | (x,i) ->
                                         let uu____6803 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____6803, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____6809 -> bs))
  
let maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            if
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
            then e
            else
              (let uu____6828 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 uu____6828 e.FStar_Syntax_Syntax.pos)
  
let maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____6854 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)
             in
          if uu____6854
          then e
          else
            (let uu____6856 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
               uu____6856 e.FStar_Syntax_Syntax.pos)
  
let effect_repr_aux only_reifiable env c =
  let uu____6893 =
    let uu____6895 =
      FStar_TypeChecker_Env.norm_eff_name env
        (FStar_Syntax_Util.comp_effect_name c)
       in
    FStar_TypeChecker_Env.effect_decl_opt env uu____6895  in
  match uu____6893 with
  | None  -> None
  | Some ed ->
      let uu____6902 =
        only_reifiable &&
          (let uu____6903 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____6903)
         in
      if uu____6902
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____6916 ->
             let nct = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                in
             let repr =
               FStar_TypeChecker_Env.inst_effect_fun_with
                 nct.FStar_TypeChecker_Env.nct_univs env ed
                 ([], (ed.FStar_Syntax_Syntax.repr))
                in
             let uu____6920 =
               let uu____6923 = FStar_TypeChecker_Env.get_range env  in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app
                    (repr,
                      (FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices
                         [nct.FStar_TypeChecker_Env.nct_result;
                         nct.FStar_TypeChecker_Env.nct_wp]))) None uu____6923
                in
             Some uu____6920)
  
let effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  = fun env  -> fun c  -> effect_repr_aux false env c 
let reify_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lc  ->
      let uu____6953 =
        let uu____6957 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
        effect_repr_aux true env uu____6957  in
      match uu____6953 with
      | None  ->
          let uu____6962 =
            let uu____6963 =
              let uu____6966 =
                FStar_Util.format1 "Effect %s cannot be reified"
                  (lc.FStar_Syntax_Syntax.lcomp_name).FStar_Ident.str
                 in
              let uu____6967 = FStar_TypeChecker_Env.get_range env  in
              (uu____6966, uu____6967)  in
            FStar_Errors.Error uu____6963  in
          Prims.raise uu____6962
      | Some tm -> tm
  
let d : Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s 
let mk_toplevel_definition :
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt *
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____6990 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____6990
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____6992 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____6992))
         else ());
        (let fv =
           let uu____6995 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____6995 None  in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [{
                FStar_Syntax_Syntax.lbname = lbname;
                FStar_Syntax_Syntax.lbunivs = [];
                FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun;
                FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid;
                FStar_Syntax_Syntax.lbdef = def
              }])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.Sig_let
             (lb, FStar_Range.dummyRange, [lident],
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen], [])
            in
         let uu____7003 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange
            in
         (sig_ctx, uu____7003))
  
let check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___100_7025 =
        match uu___100_7025 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7026 -> false  in
      let reducibility uu___101_7030 =
        match uu___101_7030 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7031 -> false  in
      let assumption uu___102_7035 =
        match uu___102_7035 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7036 -> false  in
      let reification uu___103_7040 =
        match uu___103_7040 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7042 -> false  in
      let inferred uu___104_7046 =
        match uu___104_7046 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7051 -> false  in
      let has_eq uu___105_7055 =
        match uu___105_7055 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7056 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                         (inferred x))
                        || (visibility x))
                       || (assumption x))
                      ||
                      (env.FStar_TypeChecker_Env.is_iface &&
                         (x = FStar_Syntax_Syntax.Inline_for_extraction))))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (visibility x))
                         || (reducibility x))
                        || (reification x))
                       || (inferred x))
                      ||
                      (env.FStar_TypeChecker_Env.is_iface &&
                         (x = FStar_Syntax_Syntax.Assumption))))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
          |FStar_Syntax_Syntax.Visible_default 
           |FStar_Syntax_Syntax.Irreducible 
            |FStar_Syntax_Syntax.Abstract 
             |FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq 
            ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (x = FStar_Syntax_Syntax.Abstract))
                         || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                        || (has_eq x))
                       || (inferred x))
                      || (visibility x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((reification x) || (inferred x)) || (visibility x)) ||
                      (x = FStar_Syntax_Syntax.TotalEffect)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7081 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____7084 =
        let uu____7085 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___106_7087  ->
                  match uu___106_7087 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7088 -> false))
           in
        FStar_All.pipe_right uu____7085 Prims.op_Negation  in
      if uu____7084
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____7098 =
            let uu____7099 =
              let uu____7102 =
                let uu____7103 = FStar_Syntax_Print.quals_to_string quals  in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7103 msg
                 in
              (uu____7102, r)  in
            FStar_Errors.Error uu____7099  in
          Prims.raise uu____7098  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____7111 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____7119 =
            let uu____7120 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____7120  in
          if uu____7119 then err "ill-formed combination" else ());
         (match se with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7124),uu____7125,uu____7126,uu____7127,uu____7128)
              ->
              ((let uu____7141 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____7141
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____7144 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____7144
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7148 ->
              let uu____7156 =
                let uu____7157 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____7157  in
              if uu____7156 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7161 ->
              let uu____7168 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____7168 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7171 ->
              let uu____7177 =
                let uu____7178 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____7178  in
              if uu____7177 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7182 ->
              let uu____7185 =
                let uu____7186 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____7186  in
              if uu____7185 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7190 ->
              let uu____7193 =
                let uu____7194 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____7194  in
              if uu____7193 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7198 ->
              let uu____7208 =
                let uu____7209 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____7209  in
              if uu____7208 then err'1 () else ()
          | uu____7213 -> ()))
      else ()
  
let mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q =
                        FStar_Syntax_Syntax.withinfo q
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p
                         in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee" (Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____7270 =
                            let uu____7273 =
                              let uu____7274 =
                                let uu____7279 =
                                  let uu____7280 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7280  in
                                (uu____7279, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7274  in
                            FStar_Syntax_Syntax.mk uu____7273  in
                          uu____7270 None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7306  ->
                                  match uu____7306 with
                                  | (x,imp) ->
                                      let uu____7313 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7313, imp)))
                           in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p
                         in
                      let unrefined_arg_binder =
                        let uu____7319 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7319  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv (Some p) arg_typ  in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational None
                                in
                             let uu____7328 =
                               let uu____7329 =
                                 let uu____7330 =
                                   let uu____7331 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7332 =
                                     let uu____7333 =
                                       let uu____7334 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7334
                                        in
                                     [uu____7333]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7331
                                     uu____7332
                                    in
                                 uu____7330 None p  in
                               FStar_Syntax_Util.b2t uu____7329  in
                             FStar_Syntax_Util.refine x uu____7328  in
                           let uu____7339 =
                             let uu___147_7340 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___147_7340.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___147_7340.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7339)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7350 =
                          FStar_List.map
                            (fun uu____7360  ->
                               match uu____7360 with
                               | (x,uu____7367) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps
                           in
                        FStar_List.append uu____7350 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7391  ->
                                match uu____7391 with
                                | (x,uu____7398) ->
                                    (x, (Some FStar_Syntax_Syntax.imp_tag))))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             (let uu____7407 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7407)
                               ||
                               (let uu____7408 =
                                  let uu____7409 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7409.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7408)
                              in
                           let quals =
                             let uu____7412 =
                               let uu____7414 =
                                 let uu____7416 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit)
                                    in
                                 if uu____7416
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else []  in
                               let uu____7419 =
                                 FStar_List.filter
                                   (fun uu___107_7421  ->
                                      match uu___107_7421 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7422 -> false) iquals
                                  in
                               FStar_List.append uu____7414 uu____7419  in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7412
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7435 =
                                 let uu____7436 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7436  in
                               FStar_Syntax_Syntax.mk_Total uu____7435  in
                             let uu____7437 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7437
                              in
                           let decl =
                             FStar_Syntax_Syntax.Sig_declare_typ
                               (discriminator_name, uvs, t, quals,
                                 (FStar_Ident.range_of_lid discriminator_name))
                              in
                           (let uu____7441 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7441
                            then
                              let uu____7442 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7442
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Const.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j  ->
                                             fun uu____7470  ->
                                               match uu____7470 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7486 =
                                                       let uu____7489 =
                                                         let uu____7490 =
                                                           let uu____7495 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7495,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7490
                                                          in
                                                       pos uu____7489  in
                                                     (uu____7486, b)
                                                   else
                                                     (let uu____7499 =
                                                        let uu____7502 =
                                                          let uu____7503 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7503
                                                           in
                                                        pos uu____7502  in
                                                      (uu____7499, b))))
                                      in
                                   let pat_true =
                                     let uu____7515 =
                                       let uu____7518 =
                                         let uu____7519 =
                                           let uu____7527 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq)
                                              in
                                           (uu____7527, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7519
                                          in
                                       pos uu____7518  in
                                     (uu____7515, None,
                                       FStar_Syntax_Const.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7549 =
                                       let uu____7552 =
                                         let uu____7553 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7553
                                          in
                                       pos uu____7552  in
                                     (uu____7549, None,
                                       FStar_Syntax_Const.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder)
                                      in
                                   let uu____7562 =
                                     let uu____7565 =
                                       let uu____7566 =
                                         let uu____7582 =
                                           let uu____7584 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7585 =
                                             let uu____7587 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7587]  in
                                           uu____7584 :: uu____7585  in
                                         (arg_exp, uu____7582)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7566
                                        in
                                     FStar_Syntax_Syntax.mk uu____7565  in
                                   uu____7562 None p)
                                 in
                              let dd =
                                let uu____7598 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7598
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body None  in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____7610 =
                                  let uu____7613 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None
                                     in
                                  FStar_Util.Inr uu____7613  in
                                let uu____7614 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7610;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7614
                                }  in
                              let impl =
                                let uu____7618 =
                                  let uu____7627 =
                                    let uu____7629 =
                                      let uu____7630 =
                                        FStar_All.pipe_right
                                          lb.FStar_Syntax_Syntax.lbname
                                          FStar_Util.right
                                         in
                                      FStar_All.pipe_right uu____7630
                                        (fun fv  ->
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                       in
                                    [uu____7629]  in
                                  ((false, [lb]), p, uu____7627, quals, [])
                                   in
                                FStar_Syntax_Syntax.Sig_let uu____7618  in
                              (let uu____7646 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7646
                               then
                                 let uu____7647 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7647
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7667  ->
                                  match uu____7667 with
                                  | (a,uu____7671) ->
                                      let uu____7672 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7672 with
                                       | (field_name,uu____7676) ->
                                           let field_proj_tm =
                                             let uu____7678 =
                                               let uu____7679 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7679
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7678 inst_univs
                                              in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7695 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7704  ->
                                    match uu____7704 with
                                    | (x,uu____7709) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7711 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7711 with
                                         | (field_name,uu____7716) ->
                                             let t =
                                               let uu____7718 =
                                                 let uu____7719 =
                                                   let uu____7720 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7720
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7719
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7718
                                                in
                                             let only_decl =
                                               ((let uu____7722 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env
                                                    in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7722)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7723 =
                                                    let uu____7724 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7724.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7723)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7734 =
                                                   FStar_List.filter
                                                     (fun uu___108_7736  ->
                                                        match uu___108_7736
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7737 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7734
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___109_7745  ->
                                                         match uu___109_7745
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____7746 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let decl =
                                               FStar_Syntax_Syntax.Sig_declare_typ
                                                 (field_name, uvs, t, quals1,
                                                   (FStar_Ident.range_of_lid
                                                      field_name))
                                                in
                                             ((let uu____7750 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7750
                                               then
                                                 let uu____7751 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7751
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____7778  ->
                                                             match uu____7778
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____7794
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7794,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7806
                                                                    =
                                                                    let uu____7809
                                                                    =
                                                                    let uu____7810
                                                                    =
                                                                    let uu____7815
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7815,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7810
                                                                     in
                                                                    pos
                                                                    uu____7809
                                                                     in
                                                                    (uu____7806,
                                                                    b))
                                                                   else
                                                                    (let uu____7819
                                                                    =
                                                                    let uu____7822
                                                                    =
                                                                    let uu____7823
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7823
                                                                     in
                                                                    pos
                                                                    uu____7822
                                                                     in
                                                                    (uu____7819,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7835 =
                                                     let uu____7838 =
                                                       let uu____7839 =
                                                         let uu____7847 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq)
                                                            in
                                                         (uu____7847,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7839
                                                        in
                                                     pos uu____7838  in
                                                   let uu____7853 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7835, None,
                                                     uu____7853)
                                                    in
                                                 let body =
                                                   let uu____7864 =
                                                     let uu____7867 =
                                                       let uu____7868 =
                                                         let uu____7884 =
                                                           let uu____7886 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7886]  in
                                                         (arg_exp,
                                                           uu____7884)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7868
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7867
                                                      in
                                                   uu____7864 None p1  in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None
                                                    in
                                                 let dd =
                                                   let uu____7903 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7903
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____7909 =
                                                     let uu____7912 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7912
                                                      in
                                                   let uu____7913 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7909;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7913
                                                   }  in
                                                 let impl =
                                                   let uu____7917 =
                                                     let uu____7926 =
                                                       let uu____7928 =
                                                         let uu____7929 =
                                                           FStar_All.pipe_right
                                                             lb.FStar_Syntax_Syntax.lbname
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7929
                                                           (fun fv  ->
                                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                          in
                                                       [uu____7928]  in
                                                     ((false, [lb]), p1,
                                                       uu____7926, quals1,
                                                       [])
                                                      in
                                                   FStar_Syntax_Syntax.Sig_let
                                                     uu____7917
                                                    in
                                                 (let uu____7945 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____7945
                                                  then
                                                    let uu____7946 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7946
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7695 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____7977,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____7983 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____7983 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____7996 = FStar_Syntax_Util.arrow_formals_comp t1
                      in
                   (match uu____7996 with
                    | (formals,uu____8004) ->
                        let uu____8011 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8024 =
                                   let uu____8025 =
                                     let uu____8026 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8026  in
                                   FStar_Ident.lid_equals typ_lid uu____8025
                                    in
                                 if uu____8024
                                 then
                                   match se1 with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8036,uvs',tps,typ0,uu____8040,constrs,uu____8042,uu____8043)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8057 -> failwith "Impossible"
                                 else None)
                             in
                          match tps_opt with
                          | Some x -> x
                          | None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Syntax_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Unexpected data constructor", r))
                           in
                        (match uu____8011 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8099 =
                               FStar_Syntax_Util.arrow_formals_comp typ01  in
                             (match uu____8099 with
                              | (indices,uu____8107) ->
                                  let refine_domain =
                                    let uu____8115 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___110_8117  ->
                                              match uu___110_8117 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8118 -> true
                                              | uu____8123 -> false))
                                       in
                                    if uu____8115
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___111_8130 =
                                      match uu___111_8130 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8132,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8139 -> None  in
                                    let uu____8140 =
                                      FStar_Util.find_map quals
                                        filter_records
                                       in
                                    match uu____8140 with
                                    | None  -> FStar_Syntax_Syntax.Data_ctor
                                    | Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____8148 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8148 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8179  ->
                                               fun uu____8180  ->
                                                 match (uu____8179,
                                                         uu____8180)
                                                 with
                                                 | ((x,uu____8190),(x',uu____8192))
                                                     ->
                                                     let uu____8197 =
                                                       let uu____8202 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8202)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8197) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8203 -> []
  
let destruct_comp_term :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lid * FStar_Syntax_Syntax.universes)
  =
  fun m  ->
    let uu____8209 =
      let uu____8210 = FStar_Syntax_Subst.compress m  in
      uu____8210.FStar_Syntax_Syntax.n  in
    match uu____8209 with
    | FStar_Syntax_Syntax.Tm_uinst
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = uu____8216;
           FStar_Syntax_Syntax.pos = uu____8217;
           FStar_Syntax_Syntax.vars = uu____8218;_},univs1)
        ->
        let uu____8224 = FStar_Syntax_Syntax.lid_of_fv fv  in
        (uu____8224, univs1)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8226 = FStar_Syntax_Syntax.lid_of_fv fv  in
        (uu____8226, [])
    | uu____8228 -> failwith "Impossible"
  
let mlift_of_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_TypeChecker_Env.normal_comp_typ ->
        FStar_TypeChecker_Env.normal_comp_typ
  =
  fun env  ->
    fun sub1  ->
      let mlift nct =
        let fail uu____8245 =
          let uu____8246 =
            FStar_Util.format2
              "Invalid application of mlift, effect names differ : %s vs %s"
              (FStar_Ident.text_of_lid nct.FStar_TypeChecker_Env.nct_name)
              (FStar_Ident.text_of_lid
                 (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name)
             in
          FStar_All.pipe_left failwith uu____8246  in
        let uu____8247 =
          let skeleton =
            let uu____8257 =
              let uu____8260 =
                let uu____8263 =
                  let uu____8264 =
                    let uu____8272 =
                      FStar_Syntax_Syntax.mk_Total
                        FStar_TypeChecker_Common.t_unit
                       in
                    ((sub1.FStar_Syntax_Syntax.sub_eff_binders), uu____8272)
                     in
                  FStar_Syntax_Syntax.Tm_arrow uu____8264  in
                FStar_Syntax_Syntax.mk uu____8263  in
              uu____8260 None FStar_Range.dummyRange  in
            ((sub1.FStar_Syntax_Syntax.sub_eff_univs), uu____8257)  in
          let uu____8283 = FStar_TypeChecker_Env.inst_tscheme skeleton  in
          match uu____8283 with
          | (univ_meta_vars,skel) ->
              let uu____8292 =
                FStar_List.fold_right
                  (fun univ  ->
                     fun uu____8300  ->
                       match uu____8300 with
                       | (out,i) ->
                           (((FStar_Syntax_Syntax.UN (i, univ)) :: out),
                             (i + (Prims.parse_int "1")))) univ_meta_vars
                  ([],
                    (FStar_List.length
                       sub1.FStar_Syntax_Syntax.sub_eff_binders))
                 in
              (match uu____8292 with
               | (univ_meta_vars_subst,uu____8322) ->
                   let uu____8325 =
                     maybe_instantiate env FStar_Syntax_Syntax.tun skel  in
                   (match uu____8325 with
                    | (_term,_typ,_guard,index_meta_var_subst) ->
                        let effect_binders_opening =
                          let lift_to_bvar subst_elt uu____8352 =
                            match uu____8352 with
                            | (n1,l) ->
                                (match subst_elt with
                                 | FStar_Syntax_Syntax.NT (b,uu____8367) ->
                                     ((n1 + (Prims.parse_int "1")),
                                       ((FStar_Syntax_Syntax.DB (n1, b)) ::
                                       l))
                                 | uu____8373 ->
                                     failwith "Clearly impossible")
                             in
                          let uu____8377 =
                            FStar_List.fold_right lift_to_bvar
                              index_meta_var_subst
                              ((Prims.parse_int "0"), [])
                             in
                          FStar_All.pipe_left Prims.snd uu____8377  in
                        ((FStar_List.append univ_meta_vars_subst
                            index_meta_var_subst), effect_binders_opening)))
           in
        match uu____8247 with
        | (sigma,effect_binders_opening) ->
            ((let uu____8399 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Lift")
                 in
              if uu____8399
              then
                let uu____8400 =
                  FStar_Syntax_Print.subst_to_string effect_binders_opening
                   in
                let uu____8401 = FStar_Syntax_Print.subst_to_string sigma  in
                FStar_Util.print2 "Substitution used for lift : %s and %s\n"
                  uu____8400 uu____8401
              else ());
             (let dummy_wp =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun  in
              let formal_source =
                let ct =
                  let uu___148_8407 = sub1.FStar_Syntax_Syntax.sub_eff_source
                     in
                  {
                    FStar_Syntax_Syntax.comp_typ_name =
                      (uu___148_8407.FStar_Syntax_Syntax.comp_typ_name);
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___148_8407.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_args =
                      (FStar_List.append
                         (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.effect_args
                         [dummy_wp]);
                    FStar_Syntax_Syntax.flags =
                      (uu___148_8407.FStar_Syntax_Syntax.flags)
                  }  in
                let c =
                  let uu____8413 = FStar_Syntax_Syntax.mk_Comp ct  in
                  FStar_Syntax_Subst.subst_comp effect_binders_opening
                    uu____8413
                   in
                FStar_Syntax_Subst.subst_comp sigma c  in
              let actual_source =
                let ct =
                  {
                    FStar_Syntax_Syntax.comp_typ_name =
                      (nct.FStar_TypeChecker_Env.nct_name);
                    FStar_Syntax_Syntax.comp_univs =
                      (nct.FStar_TypeChecker_Env.nct_univs);
                    FStar_Syntax_Syntax.effect_args =
                      (FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices
                         [nct.FStar_TypeChecker_Env.nct_result; dummy_wp]);
                    FStar_Syntax_Syntax.flags =
                      (nct.FStar_TypeChecker_Env.nct_flags)
                  }  in
                FStar_Syntax_Syntax.mk_Comp ct  in
              (let uu____8421 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "Lift")
                  in
               if uu____8421
               then
                 let uu____8422 =
                   FStar_Syntax_Print.comp_to_string formal_source  in
                 let uu____8423 =
                   FStar_Syntax_Print.comp_to_string actual_source  in
                 FStar_Util.print2 "trying to equate %s and %s\n" uu____8422
                   uu____8423
               else ());
              (let uu____8425 =
                 FStar_TypeChecker_Rel.sub_comp
                   (let uu___149_8427 = env  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___149_8427.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___149_8427.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___149_8427.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___149_8427.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___149_8427.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___149_8427.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___149_8427.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___149_8427.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___149_8427.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___149_8427.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___149_8427.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___149_8427.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___149_8427.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___149_8427.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___149_8427.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq = true;
                      FStar_TypeChecker_Env.is_iface =
                        (uu___149_8427.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___149_8427.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___149_8427.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___149_8427.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.type_of =
                        (uu___149_8427.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___149_8427.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___149_8427.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___149_8427.FStar_TypeChecker_Env.qname_and_index)
                    }) formal_source actual_source
                  in
               match uu____8425 with
               | None  -> fail ()
               | Some g -> FStar_TypeChecker_Rel.force_trivial_guard env g));
             (let target_nct =
                let target_wp =
                  let lift_wp =
                    let uu____8434 =
                      FStar_Util.must
                        sub1.FStar_Syntax_Syntax.sub_eff_lift_wp
                       in
                    FStar_Syntax_Subst.subst effect_binders_opening
                      uu____8434
                     in
                  let uu____8435 =
                    let uu____8436 = FStar_Syntax_Subst.subst sigma lift_wp
                       in
                    FStar_Syntax_Syntax.mk_Tm_app uu____8436
                      [nct.FStar_TypeChecker_Env.nct_wp]
                     in
                  uu____8435 None FStar_Range.dummyRange  in
                let target_comp_no_wp =
                  let c =
                    let uu____8443 =
                      FStar_Syntax_Syntax.mk_Comp
                        sub1.FStar_Syntax_Syntax.sub_eff_target
                       in
                    FStar_Syntax_Subst.subst_comp effect_binders_opening
                      uu____8443
                     in
                  let uu____8444 = FStar_Syntax_Subst.subst_comp sigma c  in
                  FStar_All.pipe_right uu____8444
                    FStar_Syntax_Util.comp_to_comp_typ
                   in
                let target_comp_typ =
                  let uu___150_8446 = target_comp_no_wp  in
                  let uu____8447 =
                    let uu____8453 =
                      let uu____8459 = FStar_Syntax_Syntax.as_arg target_wp
                         in
                      [uu____8459]  in
                    FStar_List.append
                      target_comp_no_wp.FStar_Syntax_Syntax.effect_args
                      uu____8453
                     in
                  {
                    FStar_Syntax_Syntax.comp_typ_name =
                      (uu___150_8446.FStar_Syntax_Syntax.comp_typ_name);
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___150_8446.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_args = uu____8447;
                    FStar_Syntax_Syntax.flags =
                      (uu___150_8446.FStar_Syntax_Syntax.flags)
                  }  in
                let c = FStar_Syntax_Syntax.mk_Comp target_comp_typ  in
                (let uu____8466 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "Lift")
                    in
                 if uu____8466
                 then
                   let uu____8467 = FStar_Syntax_Print.comp_to_string c  in
                   FStar_Util.print1 "Target comp type after lifting %s"
                     uu____8467
                 else ());
                FStar_TypeChecker_Env.comp_as_normal_comp_typ env c  in
              target_nct))
         in
      mlift
  
let extend_effect_lattice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun sub_eff  ->
      let compose_edges e1 e2 =
        {
          FStar_TypeChecker_Env.msource = (e1.FStar_TypeChecker_Env.msource);
          FStar_TypeChecker_Env.mtarget = (e2.FStar_TypeChecker_Env.mtarget);
          FStar_TypeChecker_Env.mlift =
            (fun nct  ->
               let uu____8484 = e1.FStar_TypeChecker_Env.mlift nct  in
               e2.FStar_TypeChecker_Env.mlift uu____8484)
        }  in
      let edge =
        let uu____8490 = mlift_of_sub_eff env sub_eff  in
        {
          FStar_TypeChecker_Env.msource =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mtarget =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mlift = uu____8490
        }  in
      let id_edge l =
        {
          FStar_TypeChecker_Env.msource = l;
          FStar_TypeChecker_Env.mtarget = l;
          FStar_TypeChecker_Env.mlift = (fun nct  -> nct)
        }  in
      let print_mlift l =
        let arg =
          let uu____8514 =
            FStar_Ident.lid_of_path ["ARG"] FStar_Range.dummyRange  in
          FStar_Syntax_Syntax.lid_as_fv uu____8514
            FStar_Syntax_Syntax.Delta_constant None
           in
        let wp =
          let uu____8516 =
            FStar_Ident.lid_of_path ["WP"] FStar_Range.dummyRange  in
          FStar_Syntax_Syntax.lid_as_fv uu____8516
            FStar_Syntax_Syntax.Delta_constant None
           in
        let uu____8517 = l arg wp  in
        FStar_Syntax_Print.term_to_string uu____8517  in
      let order = edge ::
        ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.order)  in
      let ms =
        FStar_All.pipe_right
          (env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls
          (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____8535 =
        match uu____8535 with
        | (i,j) ->
            if FStar_Ident.lid_equals i j
            then FStar_All.pipe_right (id_edge i) (fun _0_38  -> Some _0_38)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.FStar_TypeChecker_Env.msource
                         i)
                        &&
                        (FStar_Ident.lid_equals
                           e.FStar_TypeChecker_Env.mtarget j)))
         in
      let order1 =
        FStar_All.pipe_right ms
          (FStar_List.fold_left
             (fun order1  ->
                fun k  ->
                  let uu____8556 =
                    FStar_All.pipe_right ms
                      (FStar_List.collect
                         (fun i  ->
                            if FStar_Ident.lid_equals i k
                            then []
                            else
                              FStar_All.pipe_right ms
                                (FStar_List.collect
                                   (fun j  ->
                                      if FStar_Ident.lid_equals j k
                                      then []
                                      else
                                        (let uu____8568 =
                                           let uu____8573 =
                                             find_edge order1 (i, k)  in
                                           let uu____8575 =
                                             find_edge order1 (k, j)  in
                                           (uu____8573, uu____8575)  in
                                         match uu____8568 with
                                         | (Some e1,Some e2) ->
                                             let uu____8584 =
                                               compose_edges e1 e2  in
                                             [uu____8584]
                                         | uu____8585 -> [])))))
                     in
                  FStar_List.append order1 uu____8556) order)
         in
      let order2 =
        FStar_Util.remove_dups
          (fun e1  ->
             fun e2  ->
               (FStar_Ident.lid_equals e1.FStar_TypeChecker_Env.msource
                  e2.FStar_TypeChecker_Env.msource)
                 &&
                 (FStar_Ident.lid_equals e1.FStar_TypeChecker_Env.mtarget
                    e2.FStar_TypeChecker_Env.mtarget)) order1
         in
      FStar_All.pipe_right order2
        (FStar_List.iter
           (fun edge1  ->
              let uu____8597 =
                (FStar_Ident.lid_equals edge1.FStar_TypeChecker_Env.msource
                   FStar_Syntax_Const.effect_DIV_lid)
                  &&
                  (let uu____8598 =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       edge1.FStar_TypeChecker_Env.mtarget
                      in
                   FStar_All.pipe_right uu____8598
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____8597
              then
                let uu____8601 =
                  let uu____8602 =
                    let uu____8605 =
                      FStar_Util.format1
                        "Divergent computations cannot be included in an effect %s marked 'total'"
                        (edge1.FStar_TypeChecker_Env.mtarget).FStar_Ident.str
                       in
                    let uu____8606 = FStar_TypeChecker_Env.get_range env  in
                    (uu____8605, uu____8606)  in
                  FStar_Errors.Error uu____8602  in
                Prims.raise uu____8601
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           FStar_All.pipe_right ms
                             (FStar_List.fold_left
                                (fun bopt  ->
                                   fun k  ->
                                     let uu____8661 =
                                       let uu____8666 =
                                         find_edge order2 (i, k)  in
                                       let uu____8668 =
                                         find_edge order2 (j, k)  in
                                       (uu____8666, uu____8668)  in
                                     match uu____8661 with
                                     | (Some ik,Some jk) ->
                                         (match bopt with
                                          | None  -> Some (k, ik, jk)
                                          | Some (ub,uu____8691,uu____8692)
                                              ->
                                              let uu____8696 =
                                                (let uu____8697 =
                                                   find_edge order2 (k, ub)
                                                    in
                                                 FStar_Util.is_some
                                                   uu____8697)
                                                  &&
                                                  (let uu____8699 =
                                                     let uu____8700 =
                                                       find_edge order2
                                                         (ub, k)
                                                        in
                                                     FStar_Util.is_some
                                                       uu____8700
                                                      in
                                                   Prims.op_Negation
                                                     uu____8699)
                                                 in
                                              if uu____8696
                                              then Some (k, ik, jk)
                                              else bopt)
                                     | uu____8710 -> bopt) None)
                            in
                         match join_opt with
                         | None  -> []
                         | Some (k,e1,e2) ->
                             [(i, j, k, (e1.FStar_TypeChecker_Env.mlift),
                                (e2.FStar_TypeChecker_Env.mlift))]))))
          in
       let effects =
         let uu___151_8753 = env.FStar_TypeChecker_Env.effects  in
         {
           FStar_TypeChecker_Env.decls =
             (uu___151_8753.FStar_TypeChecker_Env.decls);
           FStar_TypeChecker_Env.order = order2;
           FStar_TypeChecker_Env.joins = joins
         }  in
       let uu___152_8754 = env  in
       {
         FStar_TypeChecker_Env.solver =
           (uu___152_8754.FStar_TypeChecker_Env.solver);
         FStar_TypeChecker_Env.range =
           (uu___152_8754.FStar_TypeChecker_Env.range);
         FStar_TypeChecker_Env.curmodule =
           (uu___152_8754.FStar_TypeChecker_Env.curmodule);
         FStar_TypeChecker_Env.gamma =
           (uu___152_8754.FStar_TypeChecker_Env.gamma);
         FStar_TypeChecker_Env.gamma_cache =
           (uu___152_8754.FStar_TypeChecker_Env.gamma_cache);
         FStar_TypeChecker_Env.modules =
           (uu___152_8754.FStar_TypeChecker_Env.modules);
         FStar_TypeChecker_Env.expected_typ =
           (uu___152_8754.FStar_TypeChecker_Env.expected_typ);
         FStar_TypeChecker_Env.sigtab =
           (uu___152_8754.FStar_TypeChecker_Env.sigtab);
         FStar_TypeChecker_Env.is_pattern =
           (uu___152_8754.FStar_TypeChecker_Env.is_pattern);
         FStar_TypeChecker_Env.instantiate_imp =
           (uu___152_8754.FStar_TypeChecker_Env.instantiate_imp);
         FStar_TypeChecker_Env.effects = effects;
         FStar_TypeChecker_Env.generalize =
           (uu___152_8754.FStar_TypeChecker_Env.generalize);
         FStar_TypeChecker_Env.letrecs =
           (uu___152_8754.FStar_TypeChecker_Env.letrecs);
         FStar_TypeChecker_Env.top_level =
           (uu___152_8754.FStar_TypeChecker_Env.top_level);
         FStar_TypeChecker_Env.check_uvars =
           (uu___152_8754.FStar_TypeChecker_Env.check_uvars);
         FStar_TypeChecker_Env.use_eq =
           (uu___152_8754.FStar_TypeChecker_Env.use_eq);
         FStar_TypeChecker_Env.is_iface =
           (uu___152_8754.FStar_TypeChecker_Env.is_iface);
         FStar_TypeChecker_Env.admit =
           (uu___152_8754.FStar_TypeChecker_Env.admit);
         FStar_TypeChecker_Env.lax =
           (uu___152_8754.FStar_TypeChecker_Env.lax);
         FStar_TypeChecker_Env.lax_universes =
           (uu___152_8754.FStar_TypeChecker_Env.lax_universes);
         FStar_TypeChecker_Env.type_of =
           (uu___152_8754.FStar_TypeChecker_Env.type_of);
         FStar_TypeChecker_Env.universe_of =
           (uu___152_8754.FStar_TypeChecker_Env.universe_of);
         FStar_TypeChecker_Env.use_bv_sorts =
           (uu___152_8754.FStar_TypeChecker_Env.use_bv_sorts);
         FStar_TypeChecker_Env.qname_and_index =
           (uu___152_8754.FStar_TypeChecker_Env.qname_and_index)
       })
  
let build_lattice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____8762) ->
          let uu___153_8763 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___153_8763.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___153_8763.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___153_8763.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___153_8763.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___153_8763.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___153_8763.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___153_8763.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___153_8763.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___153_8763.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___153_8763.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (let uu___154_8764 = env.FStar_TypeChecker_Env.effects  in
               {
                 FStar_TypeChecker_Env.decls = (ne ::
                   ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls));
                 FStar_TypeChecker_Env.order =
                   (uu___154_8764.FStar_TypeChecker_Env.order);
                 FStar_TypeChecker_Env.joins =
                   (uu___154_8764.FStar_TypeChecker_Env.joins)
               });
            FStar_TypeChecker_Env.generalize =
              (uu___153_8763.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___153_8763.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___153_8763.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___153_8763.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___153_8763.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___153_8763.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___153_8763.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___153_8763.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___153_8763.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___153_8763.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___153_8763.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___153_8763.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___153_8763.FStar_TypeChecker_Env.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect (sub1,uu____8766) ->
          extend_effect_lattice env sub1
      | uu____8767 -> env
  