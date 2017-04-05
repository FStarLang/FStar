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
               (let flags =
                  FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                    (FStar_List.collect
                       (fun uu___93_3356  ->
                          match uu___93_3356 with
                          | FStar_Syntax_Syntax.RETURN 
                            |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                          | uu____3358 -> []))
                   in
                let strengthen uu____3364 =
                  let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                  let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                  let uu____3369 = FStar_TypeChecker_Rel.guard_form g01  in
                  match uu____3369 with
                  | FStar_TypeChecker_Common.Trivial  -> c
                  | FStar_TypeChecker_Common.NonTrivial f ->
                      let c1 =
                        let uu____3376 =
                          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                            (let uu____3377 =
                               FStar_Syntax_Util.is_partial_return c  in
                             Prims.op_Negation uu____3377)
                           in
                        if uu____3376
                        then
                          let x =
                            let uu____3381 =
                              FStar_TypeChecker_Env.result_typ env c  in
                            FStar_Syntax_Syntax.gen_bv "strengthen_pre_x"
                              None uu____3381
                             in
                          let xret =
                            let uu____3385 =
                              let uu____3386 =
                                FStar_Syntax_Syntax.bv_to_name x  in
                              return_value env x.FStar_Syntax_Syntax.sort
                                uu____3386
                               in
                            FStar_Syntax_Util.comp_set_flags uu____3385
                              [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             in
                          let lc1 =
                            let uu____3388 =
                              FStar_TypeChecker_Env.lcomp_of_comp env c  in
                            let uu____3389 =
                              let uu____3390 =
                                FStar_TypeChecker_Env.lcomp_of_comp env xret
                                 in
                              ((Some x), uu____3390)  in
                            bind env (Some e) uu____3388 uu____3389  in
                          lc1.FStar_Syntax_Syntax.lcomp_as_comp ()
                        else c  in
                      ((let uu____3394 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            FStar_Options.Extreme
                           in
                        if uu____3394
                        then
                          let uu____3395 =
                            FStar_TypeChecker_Normalize.term_to_string env e
                             in
                          let uu____3396 =
                            FStar_TypeChecker_Normalize.term_to_string env f
                             in
                          FStar_Util.print2
                            "-------------Strengthening pre-condition of term %s with guard %s\n"
                            uu____3395 uu____3396
                        else ());
                       (let nct =
                          FStar_TypeChecker_Env.comp_as_normal_comp_typ env
                            c1
                           in
                        let md =
                          FStar_TypeChecker_Env.get_effect_decl env
                            nct.FStar_TypeChecker_Env.nct_name
                           in
                        let wp =
                          let uu____3403 =
                            let uu____3404 =
                              FStar_All.pipe_right
                                nct.FStar_TypeChecker_Env.nct_wp Prims.fst
                               in
                            uu____3404.FStar_Syntax_Syntax.pos  in
                          let uu____3411 =
                            let uu____3412 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                nct.FStar_TypeChecker_Env.nct_univs env md
                                md.FStar_Syntax_Syntax.assert_p
                               in
                            let uu____3413 =
                              let uu____3414 =
                                let uu____3420 =
                                  let uu____3422 =
                                    let uu____3423 =
                                      let uu____3424 =
                                        FStar_TypeChecker_Env.get_range env
                                         in
                                      label_opt env reason uu____3424 f  in
                                    FStar_All.pipe_left
                                      FStar_Syntax_Syntax.as_arg uu____3423
                                     in
                                  [uu____3422;
                                  nct.FStar_TypeChecker_Env.nct_wp]  in
                                (nct.FStar_TypeChecker_Env.nct_result) ::
                                  uu____3420
                                 in
                              FStar_List.append
                                nct.FStar_TypeChecker_Env.nct_indices
                                uu____3414
                               in
                            FStar_Syntax_Syntax.mk_Tm_app uu____3412
                              uu____3413
                             in
                          uu____3411 None uu____3403  in
                        (let uu____3434 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             FStar_Options.Extreme
                            in
                         if uu____3434
                         then
                           let uu____3435 =
                             FStar_Syntax_Print.term_to_string wp  in
                           FStar_Util.print1
                             "-------------Strengthened pre-condition is %s\n"
                             uu____3435
                         else ());
                        (let c2 =
                           let uu____3438 =
                             let uu___130_3439 = nct  in
                             let uu____3440 = FStar_Syntax_Syntax.as_arg wp
                                in
                             {
                               FStar_TypeChecker_Env.nct_name =
                                 (uu___130_3439.FStar_TypeChecker_Env.nct_name);
                               FStar_TypeChecker_Env.nct_univs =
                                 (uu___130_3439.FStar_TypeChecker_Env.nct_univs);
                               FStar_TypeChecker_Env.nct_indices =
                                 (uu___130_3439.FStar_TypeChecker_Env.nct_indices);
                               FStar_TypeChecker_Env.nct_result =
                                 (uu___130_3439.FStar_TypeChecker_Env.nct_result);
                               FStar_TypeChecker_Env.nct_wp = uu____3440;
                               FStar_TypeChecker_Env.nct_flags =
                                 (uu___130_3439.FStar_TypeChecker_Env.nct_flags)
                             }  in
                           FStar_TypeChecker_Env.normal_comp_typ_as_comp env
                             uu____3438
                            in
                         c2)))
                   in
                let flags1 =
                  let uu____3443 =
                    (FStar_Syntax_Util.is_pure_lcomp lc) &&
                      (let uu____3444 =
                         FStar_Syntax_Util.is_function_typ
                           lc.FStar_Syntax_Syntax.lcomp_res_typ
                          in
                       FStar_All.pipe_left Prims.op_Negation uu____3444)
                     in
                  if uu____3443 then flags else []  in
                let lc1 =
                  let uu___131_3448 = lc  in
                  {
                    FStar_Syntax_Syntax.lcomp_name =
                      (uu___131_3448.FStar_Syntax_Syntax.lcomp_name);
                    FStar_Syntax_Syntax.lcomp_univs =
                      (uu___131_3448.FStar_Syntax_Syntax.lcomp_univs);
                    FStar_Syntax_Syntax.lcomp_indices =
                      (uu___131_3448.FStar_Syntax_Syntax.lcomp_indices);
                    FStar_Syntax_Syntax.lcomp_res_typ =
                      (uu___131_3448.FStar_Syntax_Syntax.lcomp_res_typ);
                    FStar_Syntax_Syntax.lcomp_cflags = flags1;
                    FStar_Syntax_Syntax.lcomp_as_comp =
                      (uu___131_3448.FStar_Syntax_Syntax.lcomp_as_comp)
                  }  in
                let uu____3449 =
                  let uu____3450 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3450
                  then lc1
                  else
                    (let uu___132_3452 = lc1  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___132_3452.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___132_3452.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___132_3452.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ =
                         (uu___132_3452.FStar_Syntax_Syntax.lcomp_res_typ);
                       FStar_Syntax_Syntax.lcomp_cflags =
                         (uu___132_3452.FStar_Syntax_Syntax.lcomp_cflags);
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     })
                   in
                (uu____3449,
                  (let uu___133_3453 = g0  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       FStar_TypeChecker_Common.Trivial;
                     FStar_TypeChecker_Env.deferred =
                       (uu___133_3453.FStar_TypeChecker_Env.deferred);
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___133_3453.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___133_3453.FStar_TypeChecker_Env.implicits)
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
        let uu____3468 =
          let uu____3471 = FStar_Syntax_Syntax.bv_to_name x  in
          let uu____3472 = FStar_Syntax_Syntax.bv_to_name y  in
          (uu____3471, uu____3472)  in
        match uu____3468 with
        | (xexp,yexp) ->
            let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t  in
            let yret =
              let uu____3481 =
                let uu____3482 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____3483 =
                  let uu____3484 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3485 =
                    let uu____3487 = FStar_Syntax_Syntax.as_arg yexp  in
                    [uu____3487]  in
                  uu____3484 :: uu____3485  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3482 uu____3483  in
              uu____3481 None res_t.FStar_Syntax_Syntax.pos  in
            let x_eq_y_yret =
              let uu____3495 =
                let uu____3496 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                    md_pure md_pure.FStar_Syntax_Syntax.assume_p
                   in
                let uu____3497 =
                  let uu____3498 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3499 =
                    let uu____3501 =
                      let uu____3502 =
                        FStar_Syntax_Util.mk_eq2 u_res_t res_t xexp yexp  in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3502
                       in
                    let uu____3503 =
                      let uu____3505 =
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret
                         in
                      [uu____3505]  in
                    uu____3501 :: uu____3503  in
                  uu____3498 :: uu____3499  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3496 uu____3497  in
              uu____3495 None res_t.FStar_Syntax_Syntax.pos  in
            let forall_y_x_eq_y_yret =
              let uu____3513 =
                let uu____3514 =
                  FStar_TypeChecker_Env.inst_effect_fun_with
                    [u_res_t; u_res_t] env md_pure
                    md_pure.FStar_Syntax_Syntax.close_wp
                   in
                let uu____3515 =
                  let uu____3516 = FStar_Syntax_Syntax.as_arg res_t  in
                  let uu____3517 =
                    let uu____3519 = FStar_Syntax_Syntax.as_arg res_t  in
                    let uu____3520 =
                      let uu____3522 =
                        let uu____3523 =
                          let uu____3524 =
                            let uu____3528 = FStar_Syntax_Syntax.mk_binder y
                               in
                            [uu____3528]  in
                          FStar_Syntax_Util.abs uu____3524 x_eq_y_yret
                            (Some
                               (FStar_Util.Inr
                                  (FStar_Syntax_Const.effect_Tot_lid,
                                    [FStar_Syntax_Syntax.TOTAL])))
                           in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                          uu____3523
                         in
                      [uu____3522]  in
                    uu____3519 :: uu____3520  in
                  uu____3516 :: uu____3517  in
                FStar_Syntax_Syntax.mk_Tm_app uu____3514 uu____3515  in
              uu____3513 None res_t.FStar_Syntax_Syntax.pos  in
            let lc2 =
              (mk_comp md_pure) [u_res_t] [] res_t forall_y_x_eq_y_yret
                [FStar_Syntax_Syntax.PARTIAL_RETURN]
               in
            let lc =
              let uu____3544 = FStar_TypeChecker_Env.lcomp_of_comp env comp
                 in
              let uu____3545 =
                let uu____3546 = FStar_TypeChecker_Env.lcomp_of_comp env lc2
                   in
                ((Some x), uu____3546)  in
              bind env None uu____3544 uu____3545  in
            lc.FStar_Syntax_Syntax.lcomp_as_comp ()
  
let fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun lid  ->
      let uu____3554 =
        let uu____3555 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____3555  in
      FStar_Syntax_Syntax.fvar uu____3554 FStar_Syntax_Syntax.Delta_constant
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
        let uu____3571 =
          let uu____3577 =
            let uu____3583 =
              let uu____3584 = FStar_Syntax_Syntax.mk_Total res_t  in
              FStar_TypeChecker_Env.lcomp_of_comp env uu____3584  in
            (uu____3583, [])  in
          FStar_List.fold_right
            (fun uu____3597  ->
               fun uu____3598  ->
                 match (uu____3597, uu____3598) with
                 | ((formula,lc),(out,lcases1)) ->
                     let uu____3635 = join_lcomp env lc out  in
                     (match uu____3635 with
                      | (lc1,_out) -> (lc1, ((formula, lc1) :: lcases1))))
            lcases uu____3577
           in
        match uu____3571 with
        | (lc,lcases1) ->
            let bind_cases uu____3663 =
              let if_then_else1 guard cthen celse =
                let uu____3674 = lift_and_destruct env cthen celse  in
                match uu____3674 with
                | (nct_then,nct_else) ->
                    let md =
                      FStar_TypeChecker_Env.get_effect_decl env
                        nct_then.FStar_TypeChecker_Env.nct_name
                       in
                    let wp =
                      let uu____3683 =
                        FStar_Range.union_ranges
                          (Prims.fst nct_then.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                          (Prims.fst nct_else.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                         in
                      let uu____3688 =
                        let uu____3689 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            nct_then.FStar_TypeChecker_Env.nct_univs env md
                            md.FStar_Syntax_Syntax.if_then_else
                           in
                        let uu____3690 =
                          let uu____3691 =
                            let uu____3697 = FStar_Syntax_Syntax.as_arg res_t
                               in
                            let uu____3698 =
                              let uu____3700 =
                                FStar_Syntax_Syntax.as_arg guard  in
                              [uu____3700;
                              nct_then.FStar_TypeChecker_Env.nct_wp;
                              nct_else.FStar_TypeChecker_Env.nct_wp]  in
                            uu____3697 :: uu____3698  in
                          FStar_List.append
                            nct_then.FStar_TypeChecker_Env.nct_indices
                            uu____3691
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3689 uu____3690
                         in
                      uu____3688 None uu____3683  in
                    (mk_comp md) nct_then.FStar_TypeChecker_Env.nct_univs
                      nct_then.FStar_TypeChecker_Env.nct_indices res_t wp []
                 in
              let default_case =
                let post_k =
                  let uu____3711 =
                    let uu____3712 = FStar_Syntax_Syntax.null_binder res_t
                       in
                    [uu____3712]  in
                  let uu____3713 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow uu____3711 uu____3713  in
                let kwp =
                  let uu____3715 =
                    let uu____3716 = FStar_Syntax_Syntax.null_binder post_k
                       in
                    [uu____3716]  in
                  let uu____3717 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  FStar_Syntax_Util.arrow uu____3715 uu____3717  in
                let post = FStar_Syntax_Syntax.new_bv None post_k  in
                let wp =
                  let uu____3720 =
                    let uu____3724 = FStar_Syntax_Syntax.mk_binder post  in
                    [uu____3724]  in
                  let uu____3725 =
                    let uu____3726 =
                      let uu____3729 = FStar_TypeChecker_Env.get_range env
                         in
                      label FStar_TypeChecker_Err.exhaustiveness_check
                        uu____3729
                       in
                    let uu____3730 =
                      fvar_const env FStar_Syntax_Const.false_lid  in
                    FStar_All.pipe_left uu____3726 uu____3730  in
                  FStar_Syntax_Util.abs uu____3720 uu____3725
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
                  (fun uu____3745  ->
                     fun celse  ->
                       match uu____3745 with
                       | (g,cthen) ->
                           let uu____3751 =
                             cthen.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                           if_then_else1 g uu____3751 celse) lcases1
                  default_case
                 in
              let uu____3752 =
                let uu____3753 = FStar_Options.split_cases ()  in
                uu____3753 > (Prims.parse_int "0")  in
              if uu____3752
              then add_equality_to_post_condition env comp res_t
              else
                (let nct =
                   FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                 let md =
                   FStar_TypeChecker_Env.get_effect_decl env
                     nct.FStar_TypeChecker_Env.nct_name
                    in
                 let share_post_wp =
                   let uu____3762 =
                     let uu____3763 =
                       FStar_TypeChecker_Env.inst_effect_fun_with
                         nct.FStar_TypeChecker_Env.nct_univs env md
                         md.FStar_Syntax_Syntax.ite_wp
                        in
                     FStar_Syntax_Syntax.mk_Tm_app uu____3763
                       (FStar_List.append
                          nct.FStar_TypeChecker_Env.nct_indices
                          [nct.FStar_TypeChecker_Env.nct_result;
                          nct.FStar_TypeChecker_Env.nct_wp])
                      in
                   uu____3762 None
                     (Prims.fst nct.FStar_TypeChecker_Env.nct_wp).FStar_Syntax_Syntax.pos
                    in
                 (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
                   nct.FStar_TypeChecker_Env.nct_indices
                   (Prims.fst nct.FStar_TypeChecker_Env.nct_result)
                   share_post_wp [])
               in
            let uu____3776 =
              env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
            if uu____3776
            then lc
            else
              (let uu___134_3778 = lc  in
               {
                 FStar_Syntax_Syntax.lcomp_name =
                   (uu___134_3778.FStar_Syntax_Syntax.lcomp_name);
                 FStar_Syntax_Syntax.lcomp_univs =
                   (uu___134_3778.FStar_Syntax_Syntax.lcomp_univs);
                 FStar_Syntax_Syntax.lcomp_indices =
                   (uu___134_3778.FStar_Syntax_Syntax.lcomp_indices);
                 FStar_Syntax_Syntax.lcomp_res_typ =
                   (uu___134_3778.FStar_Syntax_Syntax.lcomp_res_typ);
                 FStar_Syntax_Syntax.lcomp_cflags =
                   (uu___134_3778.FStar_Syntax_Syntax.lcomp_cflags);
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
        let close1 uu____3795 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3799 = FStar_Syntax_Util.is_ml_comp c  in
          if uu____3799
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
                        let uu____3815 =
                          let uu____3817 =
                            env.FStar_TypeChecker_Env.universe_of env
                              x.FStar_Syntax_Syntax.sort
                             in
                          [uu____3817]  in
                        FStar_List.append nct.FStar_TypeChecker_Env.nct_univs
                          uu____3815
                         in
                      let wp1 =
                        let uu____3819 =
                          let uu____3823 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3823]  in
                        FStar_Syntax_Util.abs uu____3819 wp
                          (Some
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])))
                         in
                      let uu____3833 =
                        let uu____3834 =
                          FStar_TypeChecker_Env.inst_effect_fun_with us env
                            md md.FStar_Syntax_Syntax.close_wp
                           in
                        let uu____3835 =
                          let uu____3836 =
                            let uu____3842 =
                              let uu____3844 =
                                FStar_Syntax_Syntax.as_arg
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____3845 =
                                let uu____3847 =
                                  FStar_Syntax_Syntax.as_arg wp1  in
                                [uu____3847]  in
                              uu____3844 :: uu____3845  in
                            (nct.FStar_TypeChecker_Env.nct_result) ::
                              uu____3842
                             in
                          FStar_List.append
                            nct.FStar_TypeChecker_Env.nct_indices uu____3836
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____3834 uu____3835
                         in
                      uu____3833 None r) bvs
                 (Prims.fst nct.FStar_TypeChecker_Env.nct_wp)
                in
             (mk_comp md) nct.FStar_TypeChecker_Env.nct_univs
               nct.FStar_TypeChecker_Env.nct_indices
               (Prims.fst nct.FStar_TypeChecker_Env.nct_result) closed_wp
               nct.FStar_TypeChecker_Env.nct_flags)
           in
        let uu____3860 =
          env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
        if uu____3860
        then lc
        else
          (let uu___135_3862 = lc  in
           {
             FStar_Syntax_Syntax.lcomp_name =
               (uu___135_3862.FStar_Syntax_Syntax.lcomp_name);
             FStar_Syntax_Syntax.lcomp_univs =
               (uu___135_3862.FStar_Syntax_Syntax.lcomp_univs);
             FStar_Syntax_Syntax.lcomp_indices =
               (uu___135_3862.FStar_Syntax_Syntax.lcomp_indices);
             FStar_Syntax_Syntax.lcomp_res_typ =
               (uu___135_3862.FStar_Syntax_Syntax.lcomp_res_typ);
             FStar_Syntax_Syntax.lcomp_cflags =
               (uu___135_3862.FStar_Syntax_Syntax.lcomp_cflags);
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
        let refine1 uu____3877 =
          let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          let uu____3881 =
            (let uu____3882 =
               is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.lcomp_name
                in
             Prims.op_Negation uu____3882) || env.FStar_TypeChecker_Env.lax
             in
          if uu____3881
          then c
          else
            (let uu____3886 = FStar_Syntax_Util.is_partial_return c  in
             if uu____3886
             then c
             else
               (let uu____3890 =
                  (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
                    (let uu____3891 =
                       FStar_TypeChecker_Env.lid_exists env
                         FStar_Syntax_Const.effect_GTot_lid
                        in
                     Prims.op_Negation uu____3891)
                   in
                if uu____3890
                then
                  let uu____3894 =
                    let uu____3895 =
                      FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                       in
                    let uu____3896 = FStar_Syntax_Print.term_to_string e  in
                    FStar_Util.format2 "%s: %s\n" uu____3895 uu____3896  in
                  failwith uu____3894
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
                     let uu____3910 =
                       let uu____3911 = return_value env t xexp  in
                       FStar_Syntax_Util.comp_set_flags uu____3911
                         [FStar_Syntax_Syntax.PARTIAL_RETURN]
                        in
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.lcomp_of_comp env) uu____3910
                      in
                   let eq1 =
                     let uu____3913 =
                       env.FStar_TypeChecker_Env.universe_of env t  in
                     FStar_Syntax_Util.mk_eq2 uu____3913 t xexp e  in
                   let eq_ret =
                     weaken_precondition env ret1
                       (FStar_TypeChecker_Common.NonTrivial eq1)
                      in
                   let bind_lc =
                     let uu____3916 =
                       FStar_TypeChecker_Env.lcomp_of_comp env c1  in
                     bind env None uu____3916 ((Some x), eq_ret)  in
                   let uu____3918 =
                     bind_lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                   FStar_Syntax_Util.comp_set_flags uu____3918
                     (FStar_Syntax_Syntax.PARTIAL_RETURN ::
                     (FStar_Syntax_Util.comp_flags c1)))))
           in
        let flags =
          let uu____3921 =
            ((let uu____3922 =
                FStar_Syntax_Util.is_function_typ
                  lc.FStar_Syntax_Syntax.lcomp_res_typ
                 in
              Prims.op_Negation uu____3922) &&
               (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc))
              &&
              (let uu____3923 = FStar_Syntax_Util.is_lcomp_partial_return lc
                  in
               Prims.op_Negation uu____3923)
             in
          if uu____3921
          then FStar_Syntax_Syntax.PARTIAL_RETURN ::
            (lc.FStar_Syntax_Syntax.lcomp_cflags)
          else lc.FStar_Syntax_Syntax.lcomp_cflags  in
        let uu___136_3926 = lc  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (uu___136_3926.FStar_Syntax_Syntax.lcomp_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (uu___136_3926.FStar_Syntax_Syntax.lcomp_univs);
          FStar_Syntax_Syntax.lcomp_indices =
            (uu___136_3926.FStar_Syntax_Syntax.lcomp_indices);
          FStar_Syntax_Syntax.lcomp_res_typ =
            (uu___136_3926.FStar_Syntax_Syntax.lcomp_res_typ);
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
          let uu____3945 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____3945 with
          | None  ->
              let uu____3950 =
                let uu____3951 =
                  let uu____3954 =
                    FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                      env e c c'
                     in
                  let uu____3955 = FStar_TypeChecker_Env.get_range env  in
                  (uu____3954, uu____3955)  in
                FStar_Errors.Error uu____3951  in
              Prims.raise uu____3950
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
          let uu____3976 =
            let uu____3977 = FStar_Syntax_Subst.compress t  in
            uu____3977.FStar_Syntax_Syntax.n  in
          match uu____3976 with
          | FStar_Syntax_Syntax.Tm_type uu____3982 ->
              let uu____3983 =
                let uu____3984 =
                  FStar_Syntax_Subst.compress
                    lc.FStar_Syntax_Syntax.lcomp_res_typ
                   in
                uu____3984.FStar_Syntax_Syntax.n  in
              (match uu____3983 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.bool_lid
                   ->
                   let uu____3990 =
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
                     let uu____3995 =
                       let uu____3996 =
                         let uu____3997 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Util.ktype0
                            in
                         FStar_TypeChecker_Env.lcomp_of_comp env uu____3997
                          in
                       (None, uu____3996)  in
                     bind env (Some e) lc uu____3995  in
                   let e1 =
                     let uu____4002 =
                       let uu____4003 =
                         let uu____4004 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____4004]  in
                       FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____4003  in
                     uu____4002
                       (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                       e.FStar_Syntax_Syntax.pos
                      in
                   (e1, lc1)
               | uu____4011 -> (e, lc))
          | uu____4012 -> (e, lc)
  
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
              let uu____4038 =
                FStar_TypeChecker_Rel.try_teq env
                  lc.FStar_Syntax_Syntax.lcomp_res_typ t
                 in
              (uu____4038, false)
            else
              (let uu____4042 =
                 FStar_TypeChecker_Rel.try_subtype env
                   lc.FStar_Syntax_Syntax.lcomp_res_typ t
                  in
               (uu____4042, true))
             in
          match gopt with
          | (None ,uu____4048) ->
              (FStar_TypeChecker_Rel.subtype_fail env e
                 lc.FStar_Syntax_Syntax.lcomp_res_typ t;
               (e,
                 ((let uu___137_4051 = lc  in
                   {
                     FStar_Syntax_Syntax.lcomp_name =
                       (uu___137_4051.FStar_Syntax_Syntax.lcomp_name);
                     FStar_Syntax_Syntax.lcomp_univs =
                       (uu___137_4051.FStar_Syntax_Syntax.lcomp_univs);
                     FStar_Syntax_Syntax.lcomp_indices =
                       (uu___137_4051.FStar_Syntax_Syntax.lcomp_indices);
                     FStar_Syntax_Syntax.lcomp_res_typ = t;
                     FStar_Syntax_Syntax.lcomp_cflags =
                       (uu___137_4051.FStar_Syntax_Syntax.lcomp_cflags);
                     FStar_Syntax_Syntax.lcomp_as_comp =
                       (uu___137_4051.FStar_Syntax_Syntax.lcomp_as_comp)
                   })), FStar_TypeChecker_Rel.trivial_guard))
          | (Some g,apply_guard1) ->
              let uu____4055 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____4055 with
               | FStar_TypeChecker_Common.Trivial  ->
                   (e,
                     (let uu___138_4059 = lc  in
                      {
                        FStar_Syntax_Syntax.lcomp_name =
                          (uu___138_4059.FStar_Syntax_Syntax.lcomp_name);
                        FStar_Syntax_Syntax.lcomp_univs =
                          (uu___138_4059.FStar_Syntax_Syntax.lcomp_univs);
                        FStar_Syntax_Syntax.lcomp_indices =
                          (uu___138_4059.FStar_Syntax_Syntax.lcomp_indices);
                        FStar_Syntax_Syntax.lcomp_res_typ = t;
                        FStar_Syntax_Syntax.lcomp_cflags =
                          (uu___138_4059.FStar_Syntax_Syntax.lcomp_cflags);
                        FStar_Syntax_Syntax.lcomp_as_comp =
                          (uu___138_4059.FStar_Syntax_Syntax.lcomp_as_comp)
                      }), g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___139_4062 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___139_4062.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___139_4062.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___139_4062.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____4068 =
                     let uu____4069 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____4069
                     then lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify] env f
                           in
                        let uu____4074 =
                          let uu____4075 = FStar_Syntax_Subst.compress f1  in
                          uu____4075.FStar_Syntax_Syntax.n  in
                        match uu____4074 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____4080,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = uu____4082;
                                          FStar_Syntax_Syntax.pos =
                                            uu____4083;
                                          FStar_Syntax_Syntax.vars =
                                            uu____4084;_},uu____4085)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.true_lid
                            ->
                            let lc1 =
                              let uu___140_4109 = lc  in
                              {
                                FStar_Syntax_Syntax.lcomp_name =
                                  (uu___140_4109.FStar_Syntax_Syntax.lcomp_name);
                                FStar_Syntax_Syntax.lcomp_univs =
                                  (uu___140_4109.FStar_Syntax_Syntax.lcomp_univs);
                                FStar_Syntax_Syntax.lcomp_indices =
                                  (uu___140_4109.FStar_Syntax_Syntax.lcomp_indices);
                                FStar_Syntax_Syntax.lcomp_res_typ = t;
                                FStar_Syntax_Syntax.lcomp_cflags =
                                  (uu___140_4109.FStar_Syntax_Syntax.lcomp_cflags);
                                FStar_Syntax_Syntax.lcomp_as_comp =
                                  (uu___140_4109.FStar_Syntax_Syntax.lcomp_as_comp)
                              }  in
                            lc1.FStar_Syntax_Syntax.lcomp_as_comp ()
                        | uu____4110 ->
                            let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                               in
                            ((let uu____4115 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____4115
                              then
                                let uu____4116 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.lcomp_res_typ
                                   in
                                let uu____4117 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____4118 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____4119 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____4116 uu____4117 uu____4118 uu____4119
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
                                let uu____4128 =
                                  let uu____4129 =
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      nct.FStar_TypeChecker_Env.nct_univs env
                                      md md.FStar_Syntax_Syntax.ret_wp
                                     in
                                  let uu____4130 =
                                    let uu____4131 =
                                      let uu____4137 =
                                        FStar_Syntax_Syntax.as_arg t  in
                                      let uu____4138 =
                                        let uu____4140 =
                                          FStar_Syntax_Syntax.as_arg xexp  in
                                        [uu____4140]  in
                                      uu____4137 :: uu____4138  in
                                    FStar_List.append
                                      nct.FStar_TypeChecker_Env.nct_indices
                                      uu____4131
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____4129
                                    uu____4130
                                   in
                                uu____4128 None xexp.FStar_Syntax_Syntax.pos
                                 in
                              let cret =
                                let uu____4150 =
                                  (mk_comp md)
                                    nct.FStar_TypeChecker_Env.nct_univs
                                    nct.FStar_TypeChecker_Env.nct_indices t
                                    wp [FStar_Syntax_Syntax.RETURN]
                                   in
                                FStar_TypeChecker_Env.lcomp_of_comp env
                                  uu____4150
                                 in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____4156 =
                                    let uu____4157 =
                                      let uu____4158 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____4158]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____4157
                                     in
                                  uu____4156
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____4164 =
                                let uu____4167 =
                                  FStar_All.pipe_left
                                    (fun _0_28  -> Some _0_28)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env
                                       lc.FStar_Syntax_Syntax.lcomp_res_typ t)
                                   in
                                let uu____4178 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____4179 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____4167 uu____4178
                                  e cret uu____4179
                                 in
                              match uu____4164 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___141_4185 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___141_4185.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___141_4185.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.lcomp_res_typ)
                                    }  in
                                  let c1 =
                                    let uu____4187 =
                                      let uu____4188 =
                                        FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                          env nct
                                         in
                                      FStar_TypeChecker_Env.lcomp_of_comp env
                                        uu____4188
                                       in
                                    bind env (Some e) uu____4187
                                      ((Some x1), eq_ret)
                                     in
                                  let c2 =
                                    c1.FStar_Syntax_Syntax.lcomp_as_comp ()
                                     in
                                  ((let uu____4194 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____4194
                                    then
                                      let uu____4195 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____4195
                                    else ());
                                   c2))))
                      in
                   let flags =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
                       (FStar_List.collect
                          (fun uu___94_4201  ->
                             match uu___94_4201 with
                             | FStar_Syntax_Syntax.RETURN 
                               |FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____4203 -> []))
                      in
                   let lc1 =
                     let uu___142_4205 = lc  in
                     {
                       FStar_Syntax_Syntax.lcomp_name =
                         (uu___142_4205.FStar_Syntax_Syntax.lcomp_name);
                       FStar_Syntax_Syntax.lcomp_univs =
                         (uu___142_4205.FStar_Syntax_Syntax.lcomp_univs);
                       FStar_Syntax_Syntax.lcomp_indices =
                         (uu___142_4205.FStar_Syntax_Syntax.lcomp_indices);
                       FStar_Syntax_Syntax.lcomp_res_typ = t;
                       FStar_Syntax_Syntax.lcomp_cflags = flags;
                       FStar_Syntax_Syntax.lcomp_as_comp = strengthen
                     }  in
                   let g2 =
                     let uu___143_4207 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___143_4207.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___143_4207.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___143_4207.FStar_TypeChecker_Env.implicits)
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
        let uu____4227 =
          let uu____4228 =
            let uu____4229 =
              let uu____4230 =
                let uu____4231 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____4231  in
              [uu____4230]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____4229  in
          uu____4228 None res_t.FStar_Syntax_Syntax.pos  in
        FStar_Syntax_Util.refine x uu____4227  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____4240 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____4240
      then
        let uu____4244 = FStar_TypeChecker_Env.result_typ env comp  in
        (None, uu____4244)
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
                | (res,uu____4263)::(req,uu____4265)::(ens,uu____4267)::uu____4268
                    ->
                    let uu____4298 =
                      let uu____4300 = norm req  in Some uu____4300  in
                    let uu____4301 =
                      let uu____4302 = mk_post_type res ens  in
                      FStar_All.pipe_left norm uu____4302  in
                    (uu____4298, uu____4301)
                | uu____4304 ->
                    let uu____4310 =
                      let uu____4311 =
                        let uu____4314 =
                          let uu____4315 =
                            FStar_Syntax_Print.comp_to_string comp  in
                          FStar_Util.format1
                            "Effect constructor is not fully applied; got %s"
                            uu____4315
                           in
                        (uu____4314, (comp.FStar_Syntax_Syntax.pos))  in
                      FStar_Errors.Error uu____4311  in
                    Prims.raise uu____4310)
             else
               (let nct =
                  FStar_TypeChecker_Env.comp_as_normal_comp_typ env comp  in
                let res_t = Prims.fst nct.FStar_TypeChecker_Env.nct_result
                   in
                let wp = Prims.fst nct.FStar_TypeChecker_Env.nct_wp  in
                let uu____4331 =
                  FStar_TypeChecker_Env.lookup_lid env
                    FStar_Syntax_Const.as_requires
                   in
                match uu____4331 with
                | (us_r,uu____4338) ->
                    let uu____4339 =
                      FStar_TypeChecker_Env.lookup_lid env
                        FStar_Syntax_Const.as_ensures
                       in
                    (match uu____4339 with
                     | (us_e,uu____4346) ->
                         let r = res_t.FStar_Syntax_Syntax.pos  in
                         let as_req =
                           let uu____4349 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_requires r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst uu____4349 us_r
                            in
                         let as_ens =
                           let uu____4351 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.as_ensures r)
                               FStar_Syntax_Syntax.Delta_equational None
                              in
                           FStar_Syntax_Syntax.mk_Tm_uinst uu____4351 us_e
                            in
                         let req =
                           let uu____4355 =
                             let uu____4356 =
                               let uu____4357 =
                                 let uu____4364 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____4364]  in
                               (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                 uu____4357
                                in
                             FStar_Syntax_Syntax.mk_Tm_app as_req uu____4356
                              in
                           uu____4355
                             (Some
                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                             r
                            in
                         let ens =
                           let uu____4380 =
                             let uu____4381 =
                               let uu____4382 =
                                 let uu____4389 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____4389]  in
                               (res_t, (Some FStar_Syntax_Syntax.imp_tag)) ::
                                 uu____4382
                                in
                             FStar_Syntax_Syntax.mk_Tm_app as_ens uu____4381
                              in
                           uu____4380 None r  in
                         let uu____4402 =
                           let uu____4404 = norm req  in Some uu____4404  in
                         let uu____4405 =
                           let uu____4406 = mk_post_type res_t ens  in
                           norm uu____4406  in
                         (uu____4402, uu____4405))))
  
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
             let uu____4436 = FStar_Syntax_Util.arrow_formals_comp t1  in
             match uu____4436 with
             | (formals,uu____4443) ->
                 let n_implicits =
                   let uu____4451 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____4488  ->
                             match uu____4488 with
                             | (uu____4492,imp) ->
                                 (imp = None) ||
                                   (imp = (Some FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____4451 with
                   | None  -> FStar_List.length formals
                   | Some (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____4564 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____4564 with
             | None  -> None
             | Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____4578 =
                     let uu____4579 =
                       let uu____4582 =
                         let uu____4583 = FStar_Util.string_of_int n_expected
                            in
                         let uu____4587 = FStar_Syntax_Print.term_to_string e
                            in
                         let uu____4588 =
                           FStar_Util.string_of_int n_available  in
                         FStar_Util.format3
                           "Expected a term with %s implicit arguments, but %s has only %s"
                           uu____4583 uu____4587 uu____4588
                          in
                       let uu____4592 = FStar_TypeChecker_Env.get_range env
                          in
                       (uu____4582, uu____4592)  in
                     FStar_Errors.Error uu____4579  in
                   Prims.raise uu____4578
                 else Some (n_available - n_expected)
              in
           let decr_inst uu___95_4605 =
             match uu___95_4605 with
             | None  -> None
             | Some i -> Some (i - (Prims.parse_int "1"))  in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____4625 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____4625 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (Some _0_29,uu____4687) when
                          _0_29 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____4709,(x,Some (FStar_Syntax_Syntax.Implicit
                                     dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____4728 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____4728 with
                           | (v1,uu____4749,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____4759 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____4759 with
                                | (args,bs3,subst3,g') ->
                                    let uu____4808 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____4808)))
                      | (uu____4822,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____4846 =
                      let uu____4860 = inst_n_binders t  in
                      aux [] uu____4860 bs1  in
                    (match uu____4846 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____4900) -> (e, torig, guard, [])
                          | (uu____4917,[]) when
                              let uu____4933 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____4933 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard,
                                [])
                          | uu____4935 ->
                              let t1 =
                                match bs2 with
                                | [] ->
                                    FStar_TypeChecker_Env.result_typ env c1
                                | uu____4950 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                (FStar_Syntax_Syntax.mk_Tm_app e args)
                                  (Some (t2.FStar_Syntax_Syntax.n))
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard, subst1))))
           | uu____4966 -> (e, t, FStar_TypeChecker_Rel.trivial_guard, []))
  
let string_of_univs univs1 =
  let uu____4979 =
    let uu____4981 = FStar_Util.set_elements univs1  in
    FStar_All.pipe_right uu____4981
      (FStar_List.map
         (fun u  ->
            let uu____4991 = FStar_Unionfind.uvar_id u  in
            FStar_All.pipe_right uu____4991 FStar_Util.string_of_int))
     in
  FStar_All.pipe_right uu____4979 (FStar_String.concat ", ") 
let gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list
  =
  fun env  ->
    fun x  ->
      let uu____5003 = FStar_Util.set_is_empty x  in
      if uu____5003
      then []
      else
        (let s =
           let uu____5008 =
             let uu____5010 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____5010  in
           FStar_All.pipe_right uu____5008 FStar_Util.set_elements  in
         (let uu____5015 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____5015
          then
            let uu____5016 =
              let uu____5017 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____5017  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____5016
          else ());
         (let r =
            let uu____5025 = FStar_TypeChecker_Env.get_range env  in
            Some uu____5025  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____5037 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____5037
                     then
                       let uu____5038 =
                         let uu____5039 = FStar_Unionfind.uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____5039
                          in
                       let uu____5041 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____5042 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____5038 uu____5041 uu____5042
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
        let uu____5059 =
          FStar_Util.fifo_set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____5059 FStar_Util.fifo_set_elements  in
      univnames1
  
let maybe_set_tk ts uu___96_5086 =
  match uu___96_5086 with
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
        | ([],uu____5127) -> generalized_univ_names
        | (uu____5131,[]) -> explicit_univ_names
        | uu____5135 ->
            let uu____5140 =
              let uu____5141 =
                let uu____5144 =
                  let uu____5145 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "Generalized universe in a term containing explicit universe annotation : "
                    uu____5145
                   in
                (uu____5144, (t.FStar_Syntax_Syntax.pos))  in
              FStar_Errors.Error uu____5141  in
            Prims.raise uu____5140
  
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
      (let uu____5158 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____5158
       then
         let uu____5159 = string_of_univs univs1  in
         FStar_Util.print1 "univs to gen : %s\n" uu____5159
       else ());
      (let gen1 = gen_univs env univs1  in
       (let uu____5165 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____5165
        then
          let uu____5166 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.print1 "After generalization: %s\n" uu____5166
        else ());
       (let univs2 = check_universe_generalization univnames1 gen1 t0  in
        let ts = FStar_Syntax_Subst.close_univ_vars univs2 t  in
        let uu____5171 = FStar_ST.read t0.FStar_Syntax_Syntax.tk  in
        maybe_set_tk (univs2, ts) uu____5171))
  
let gen :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list ->
      (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list Prims.option
  =
  fun env  ->
    fun ecs  ->
      let uu____5201 =
        let uu____5202 =
          FStar_Util.for_all
            (fun uu____5207  ->
               match uu____5207 with
               | (uu____5212,c) -> FStar_Syntax_Util.is_pure_or_ghost_comp c)
            ecs
           in
        FStar_All.pipe_left Prims.op_Negation uu____5202  in
      if uu____5201
      then None
      else
        (let norm c =
           (let uu____5235 =
              FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
            if uu____5235
            then
              let uu____5236 = FStar_Syntax_Print.comp_to_string c  in
              FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                uu____5236
            else ());
           (let c1 =
              let uu____5239 = FStar_TypeChecker_Env.should_verify env  in
              if uu____5239
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
            (let uu____5242 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____5242
             then
               let uu____5243 = FStar_Syntax_Print.comp_to_string c1  in
               FStar_Util.print1 "Normalized to:\n\t %s\n" uu____5243
             else ());
            c1)
            in
         let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
         let gen_uvars uvs =
           let uu____5277 = FStar_Util.set_difference uvs env_uvars  in
           FStar_All.pipe_right uu____5277 FStar_Util.set_elements  in
         let uu____5321 =
           let uu____5339 =
             FStar_All.pipe_right ecs
               (FStar_List.map
                  (fun uu____5392  ->
                     match uu____5392 with
                     | (e,c) ->
                         let c1 = norm c  in
                         let t =
                           let uu____5414 =
                             FStar_TypeChecker_Env.result_typ env c1  in
                           FStar_All.pipe_right uu____5414
                             FStar_Syntax_Subst.compress
                            in
                         let univs1 = FStar_Syntax_Free.univs t  in
                         let uvt = FStar_Syntax_Free.uvars t  in
                         let uvs = gen_uvars uvt  in (univs1, (uvs, e, c1))))
              in
           FStar_All.pipe_right uu____5339 FStar_List.unzip  in
         match uu____5321 with
         | (univs1,uvars1) ->
             let univs2 =
               FStar_List.fold_left FStar_Util.set_union
                 FStar_Syntax_Syntax.no_universe_uvars univs1
                in
             let gen_univs1 = gen_univs env univs2  in
             ((let uu____5544 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____5544
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
                      (fun uu____5586  ->
                         match uu____5586 with
                         | (uvs,e,c) ->
                             let tvars =
                               FStar_All.pipe_right uvs
                                 (FStar_List.map
                                    (fun uu____5643  ->
                                       match uu____5643 with
                                       | (u,k) ->
                                           let uu____5663 =
                                             FStar_Unionfind.find u  in
                                           (match uu____5663 with
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
                                                uu____5701 ->
                                                failwith
                                                  "Unexpected instantiation of mutually recursive uvar"
                                            | uu____5709 ->
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env k
                                                   in
                                                let uu____5714 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    k1
                                                   in
                                                (match uu____5714 with
                                                 | (bs,cres) ->
                                                     let kres =
                                                       FStar_TypeChecker_Env.result_typ
                                                         env cres
                                                        in
                                                     let a =
                                                       let uu____5733 =
                                                         let uu____5735 =
                                                           FStar_TypeChecker_Env.get_range
                                                             env
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _0_30  ->
                                                              Some _0_30)
                                                           uu____5735
                                                          in
                                                       FStar_Syntax_Syntax.new_bv
                                                         uu____5733 kres
                                                        in
                                                     let t =
                                                       let uu____5738 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       let uu____5739 =
                                                         let uu____5746 =
                                                           let uu____5752 =
                                                             let uu____5753 =
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 kres
                                                                in
                                                             FStar_TypeChecker_Env.lcomp_of_comp
                                                               env uu____5753
                                                              in
                                                           FStar_Util.Inl
                                                             uu____5752
                                                            in
                                                         Some uu____5746  in
                                                       FStar_Syntax_Util.abs
                                                         bs uu____5738
                                                         uu____5739
                                                        in
                                                     (FStar_Syntax_Util.set_uvar
                                                        u t;
                                                      (a,
                                                        (Some
                                                           FStar_Syntax_Syntax.imp_tag)))))))
                                in
                             let uu____5766 =
                               match (tvars, gen_univs1) with
                               | ([],[]) -> (e, c)
                               | ([],uu____5784) ->
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
                               | uu____5796 ->
                                   let uu____5804 = (e, c)  in
                                   (match uu____5804 with
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
                                          let uu____5814 =
                                            let uu____5815 =
                                              let uu____5818 =
                                                FStar_TypeChecker_Env.result_typ
                                                  env c1
                                                 in
                                              FStar_Syntax_Subst.compress
                                                uu____5818
                                               in
                                            uu____5815.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5814 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____5831 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____5831 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append tvars
                                                        bs1) cod1)
                                          | uu____5839 ->
                                              FStar_Syntax_Util.arrow tvars
                                                c1
                                           in
                                        let e' =
                                          let uu____5841 =
                                            let uu____5848 =
                                              let uu____5854 =
                                                FStar_TypeChecker_Env.lcomp_of_comp
                                                  env c1
                                                 in
                                              FStar_Util.Inl uu____5854  in
                                            Some uu____5848  in
                                          FStar_Syntax_Util.abs tvars e1
                                            uu____5841
                                           in
                                        let uu____5863 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____5863))
                                in
                             (match uu____5766 with
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
      (let uu____5901 = FStar_TypeChecker_Env.debug env FStar_Options.Low  in
       if uu____5901
       then
         let uu____5902 =
           let uu____5903 =
             FStar_List.map
               (fun uu____5908  ->
                  match uu____5908 with
                  | (lb,uu____5913,uu____5914) ->
                      FStar_Syntax_Print.lbname_to_string lb) lecs
              in
           FStar_All.pipe_right uu____5903 (FStar_String.concat ", ")  in
         FStar_Util.print1 "Generalizing: %s\n" uu____5902
       else ());
      (let univnames_lecs =
         FStar_List.map
           (fun uu____5922  ->
              match uu____5922 with | (l,t,c) -> gather_free_univnames env t)
           lecs
          in
       let generalized_lecs =
         let uu____5936 =
           let uu____5943 =
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5959  ->
                     match uu____5959 with | (uu____5965,e,c) -> (e, c)))
              in
           gen env uu____5943  in
         match uu____5936 with
         | None  ->
             FStar_All.pipe_right lecs
               (FStar_List.map
                  (fun uu____5997  ->
                     match uu____5997 with | (l,t,c) -> (l, [], t, c)))
         | Some ecs ->
             FStar_List.map2
               (fun uu____6037  ->
                  fun uu____6038  ->
                    match (uu____6037, uu____6038) with
                    | ((l,uu____6065,uu____6066),(us,e,c)) ->
                        ((let uu____6086 =
                            FStar_TypeChecker_Env.debug env
                              FStar_Options.Medium
                             in
                          if uu____6086
                          then
                            let uu____6087 =
                              FStar_Range.string_of_range
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____6088 =
                              FStar_Syntax_Print.lbname_to_string l  in
                            let uu____6089 =
                              let uu____6090 =
                                FStar_TypeChecker_Env.result_typ env c  in
                              FStar_Syntax_Print.term_to_string uu____6090
                               in
                            let uu____6091 =
                              FStar_Syntax_Print.term_to_string e  in
                            FStar_Util.print4
                              "(%s) Generalized %s at type %s\n%s\n"
                              uu____6087 uu____6088 uu____6089 uu____6091
                          else ());
                         (l, us, e, c))) lecs ecs
          in
       FStar_List.map2
         (fun univnames1  ->
            fun uu____6108  ->
              match uu____6108 with
              | (l,generalized_univs,t,c) ->
                  let uu____6126 =
                    check_universe_generalization univnames1
                      generalized_univs t
                     in
                  (l, uu____6126, t, c)) univnames_lecs generalized_lecs)
  
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
              (let uu____6159 =
                 FStar_TypeChecker_Rel.try_subtype env2 t11 t21  in
               match uu____6159 with
               | None  -> None
               | Some f ->
                   let uu____6163 = FStar_TypeChecker_Rel.apply_guard f e  in
                   FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____6163)
             in
          let is_var e1 =
            let uu____6169 =
              let uu____6170 = FStar_Syntax_Subst.compress e1  in
              uu____6170.FStar_Syntax_Syntax.n  in
            match uu____6169 with
            | FStar_Syntax_Syntax.Tm_name uu____6173 -> true
            | uu____6174 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_name
                      (let uu___144_6196 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___144_6196.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___144_6196.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t2
                       }))) (Some (t2.FStar_Syntax_Syntax.n))
                  e2.FStar_Syntax_Syntax.pos
            | uu____6197 ->
                let uu___145_6198 = e2  in
                let uu____6199 =
                  FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n))  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___145_6198.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk = uu____6199;
                  FStar_Syntax_Syntax.pos =
                    (uu___145_6198.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___145_6198.FStar_Syntax_Syntax.vars)
                }
             in
          let env2 =
            let uu___146_6208 = env1  in
            let uu____6209 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_6208.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_6208.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_6208.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_6208.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_6208.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_6208.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_6208.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_6208.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_6208.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_6208.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_6208.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_6208.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_6208.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___146_6208.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_6208.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____6209;
              FStar_TypeChecker_Env.is_iface =
                (uu___146_6208.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_6208.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_6208.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_6208.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___146_6208.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_6208.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_6208.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_6208.FStar_TypeChecker_Env.qname_and_index)
            }  in
          let uu____6210 = check env2 t1 t2  in
          match uu____6210 with
          | None  ->
              let uu____6214 =
                let uu____6215 =
                  let uu____6218 =
                    FStar_TypeChecker_Err.expected_expression_of_type env2 t2
                      e t1
                     in
                  let uu____6219 = FStar_TypeChecker_Env.get_range env2  in
                  (uu____6218, uu____6219)  in
                FStar_Errors.Error uu____6215  in
              Prims.raise uu____6214
          | Some g ->
              ((let uu____6224 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____6224
                then
                  let uu____6225 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____6225
                else ());
               (let uu____6227 = decorate e t2  in (uu____6227, g)))
  
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
        let uu____6251 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____6251
        then
          let uu____6254 = discharge g1  in
          let uu____6255 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
          (uu____6254, uu____6255)
        else
          (let c = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
           let steps = [FStar_TypeChecker_Normalize.Beta]  in
           let c1 =
             let uu____6267 =
               let uu____6268 =
                 let uu____6269 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____6269 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____6268
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____6267
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let nct =
             let uu____6271 = FStar_Syntax_Syntax.mk_Comp c1  in
             FStar_TypeChecker_Env.comp_as_normal_comp_typ env uu____6271  in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               nct.FStar_TypeChecker_Env.nct_name
              in
           let vc =
             let uu____6276 = FStar_TypeChecker_Env.get_range env  in
             let uu____6277 =
               let uu____6278 =
                 FStar_TypeChecker_Env.inst_effect_fun_with
                   nct.FStar_TypeChecker_Env.nct_univs env md
                   md.FStar_Syntax_Syntax.trivial
                  in
               FStar_Syntax_Syntax.mk_Tm_app uu____6278
                 (FStar_List.append nct.FStar_TypeChecker_Env.nct_indices
                    [nct.FStar_TypeChecker_Env.nct_result;
                    nct.FStar_TypeChecker_Env.nct_wp])
                in
             uu____6277
               (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
               uu____6276
              in
           (let uu____6288 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____6288
            then
              let uu____6289 = FStar_Syntax_Print.term_to_string vc  in
              FStar_Util.print1 "top-level VC: %s\n" uu____6289
            else ());
           (let g2 =
              let uu____6292 =
                FStar_All.pipe_left
                  FStar_TypeChecker_Rel.guard_of_guard_formula
                  (FStar_TypeChecker_Common.NonTrivial vc)
                 in
              FStar_TypeChecker_Rel.conj_guard g1 uu____6292  in
            let uu____6293 = discharge g2  in
            let uu____6294 = FStar_Syntax_Syntax.mk_Comp c1  in
            (uu____6293, uu____6294)))
  
let short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___97_6318 =
        match uu___97_6318 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____6324)::[] -> f fst1
        | uu____6337 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____6342 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____6342
          (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32)
         in
      let op_or_e e =
        let uu____6351 =
          let uu____6354 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____6354  in
        FStar_All.pipe_right uu____6351
          (fun _0_33  -> FStar_TypeChecker_Common.NonTrivial _0_33)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34)
         in
      let op_or_t t =
        let uu____6365 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____6365
          (fun _0_35  -> FStar_TypeChecker_Common.NonTrivial _0_35)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_36  -> FStar_TypeChecker_Common.NonTrivial _0_36)
         in
      let short_op_ite uu___98_6379 =
        match uu___98_6379 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____6385)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____6400)::[] ->
            let uu____6421 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____6421
              (fun _0_37  -> FStar_TypeChecker_Common.NonTrivial _0_37)
        | uu____6426 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____6433 =
          let uu____6438 = short_bin_op op_and_e  in
          (FStar_Syntax_Const.op_And, uu____6438)  in
        let uu____6443 =
          let uu____6449 =
            let uu____6454 = short_bin_op op_or_e  in
            (FStar_Syntax_Const.op_Or, uu____6454)  in
          let uu____6459 =
            let uu____6465 =
              let uu____6470 = short_bin_op op_and_t  in
              (FStar_Syntax_Const.and_lid, uu____6470)  in
            let uu____6475 =
              let uu____6481 =
                let uu____6486 = short_bin_op op_or_t  in
                (FStar_Syntax_Const.or_lid, uu____6486)  in
              let uu____6491 =
                let uu____6497 =
                  let uu____6502 = short_bin_op op_imp_t  in
                  (FStar_Syntax_Const.imp_lid, uu____6502)  in
                [uu____6497; (FStar_Syntax_Const.ite_lid, short_op_ite)]  in
              uu____6481 :: uu____6491  in
            uu____6465 :: uu____6475  in
          uu____6449 :: uu____6459  in
        uu____6433 :: uu____6443  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____6543 =
            FStar_Util.find_map table
              (fun uu____6549  ->
                 match uu____6549 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then let uu____6562 = mk1 seen_args  in Some uu____6562
                     else None)
             in
          (match uu____6543 with
           | None  -> FStar_TypeChecker_Common.Trivial
           | Some g -> g)
      | uu____6565 -> FStar_TypeChecker_Common.Trivial
  
let short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool =
  fun l  ->
    let uu____6569 =
      let uu____6570 = FStar_Syntax_Util.un_uinst l  in
      uu____6570.FStar_Syntax_Syntax.n  in
    match uu____6569 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Syntax_Const.op_And;
          FStar_Syntax_Const.op_Or;
          FStar_Syntax_Const.and_lid;
          FStar_Syntax_Const.or_lid;
          FStar_Syntax_Const.imp_lid;
          FStar_Syntax_Const.ite_lid]
    | uu____6574 -> false
  
let maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____6592)::uu____6593 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____6599 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____6603,Some (FStar_Syntax_Syntax.Implicit uu____6604))::uu____6605
          -> bs
      | uu____6614 ->
          let uu____6615 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____6615 with
           | None  -> bs
           | Some t ->
               let uu____6618 =
                 let uu____6619 = FStar_Syntax_Subst.compress t  in
                 uu____6619.FStar_Syntax_Syntax.n  in
               (match uu____6618 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____6623) ->
                    let uu____6634 =
                      FStar_Util.prefix_until
                        (fun uu___99_6653  ->
                           match uu___99_6653 with
                           | (uu____6657,Some (FStar_Syntax_Syntax.Implicit
                              uu____6658)) -> false
                           | uu____6660 -> true) bs'
                       in
                    (match uu____6634 with
                     | None  -> bs
                     | Some ([],uu____6678,uu____6679) -> bs
                     | Some (imps,uu____6716,uu____6717) ->
                         let uu____6754 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____6762  ->
                                   match uu____6762 with
                                   | (x,uu____6767) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____6754
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____6790  ->
                                     match uu____6790 with
                                     | (x,i) ->
                                         let uu____6801 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____6801, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____6807 -> bs))
  
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
              (let uu____6826 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
               (FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_meta
                     (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)))))
                 uu____6826 e.FStar_Syntax_Syntax.pos)
  
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
          let uu____6852 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)
             in
          if uu____6852
          then e
          else
            (let uu____6854 = FStar_ST.read e.FStar_Syntax_Syntax.tk  in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic (m, t)))))
               uu____6854 e.FStar_Syntax_Syntax.pos)
  
let effect_repr_aux only_reifiable env c =
  let uu____6891 =
    let uu____6893 =
      FStar_TypeChecker_Env.norm_eff_name env
        (FStar_Syntax_Util.comp_effect_name c)
       in
    FStar_TypeChecker_Env.effect_decl_opt env uu____6893  in
  match uu____6891 with
  | None  -> None
  | Some ed ->
      let uu____6900 =
        only_reifiable &&
          (let uu____6901 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____6901)
         in
      if uu____6900
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____6914 ->
             let nct = FStar_TypeChecker_Env.comp_as_normal_comp_typ env c
                in
             let repr =
               FStar_TypeChecker_Env.inst_effect_fun_with
                 nct.FStar_TypeChecker_Env.nct_univs env ed
                 ([], (ed.FStar_Syntax_Syntax.repr))
                in
             let uu____6918 =
               let uu____6921 = FStar_TypeChecker_Env.get_range env  in
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app
                    (repr,
                      (FStar_List.append
                         nct.FStar_TypeChecker_Env.nct_indices
                         [nct.FStar_TypeChecker_Env.nct_result;
                         nct.FStar_TypeChecker_Env.nct_wp]))) None uu____6921
                in
             Some uu____6918)
  
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
      let uu____6951 =
        let uu____6955 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()  in
        effect_repr_aux true env uu____6955  in
      match uu____6951 with
      | None  ->
          let uu____6960 =
            let uu____6961 =
              let uu____6964 =
                FStar_Util.format1 "Effect %s cannot be reified"
                  (lc.FStar_Syntax_Syntax.lcomp_name).FStar_Ident.str
                 in
              let uu____6965 = FStar_TypeChecker_Env.get_range env  in
              (uu____6964, uu____6965)  in
            FStar_Errors.Error uu____6961  in
          Prims.raise uu____6960
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
        (let uu____6988 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____6988
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____6990 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____6990))
         else ());
        (let fv =
           let uu____6993 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____6993 None  in
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
         let uu____7001 =
           (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)) None
             FStar_Range.dummyRange
            in
         (sig_ctx, uu____7001))
  
let check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      let visibility uu___100_7023 =
        match uu___100_7023 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____7024 -> false  in
      let reducibility uu___101_7028 =
        match uu___101_7028 with
        | FStar_Syntax_Syntax.Abstract 
          |FStar_Syntax_Syntax.Irreducible 
           |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
            |FStar_Syntax_Syntax.Visible_default 
             |FStar_Syntax_Syntax.Inline_for_extraction 
            -> true
        | uu____7029 -> false  in
      let assumption uu___102_7033 =
        match uu___102_7033 with
        | FStar_Syntax_Syntax.Assumption |FStar_Syntax_Syntax.New  -> true
        | uu____7034 -> false  in
      let reification uu___103_7038 =
        match uu___103_7038 with
        | FStar_Syntax_Syntax.Reifiable |FStar_Syntax_Syntax.Reflectable _ ->
            true
        | uu____7040 -> false  in
      let inferred uu___104_7044 =
        match uu___104_7044 with
        | FStar_Syntax_Syntax.Discriminator _
          |FStar_Syntax_Syntax.Projector _
           |FStar_Syntax_Syntax.RecordType _
            |FStar_Syntax_Syntax.RecordConstructor _
             |FStar_Syntax_Syntax.ExceptionConstructor 
              |FStar_Syntax_Syntax.HasMaskedEffect 
               |FStar_Syntax_Syntax.Effect 
            -> true
        | uu____7049 -> false  in
      let has_eq uu___105_7053 =
        match uu___105_7053 with
        | FStar_Syntax_Syntax.Noeq |FStar_Syntax_Syntax.Unopteq  -> true
        | uu____7054 -> false  in
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
        | uu____7079 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____7082 =
        let uu____7083 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___106_7085  ->
                  match uu___106_7085 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7086 -> false))
           in
        FStar_All.pipe_right uu____7083 Prims.op_Negation  in
      if uu____7082
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____7096 =
            let uu____7097 =
              let uu____7100 =
                let uu____7101 = FStar_Syntax_Print.quals_to_string quals  in
                FStar_Util.format2
                  "The qualifier list \"[%s]\" is not permissible for this element%s"
                  uu____7101 msg
                 in
              (uu____7100, r)  in
            FStar_Errors.Error uu____7097  in
          Prims.raise uu____7096  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____7109 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____7117 =
            let uu____7118 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____7118  in
          if uu____7117 then err "ill-formed combination" else ());
         (match se with
          | FStar_Syntax_Syntax.Sig_let
              ((is_rec,uu____7122),uu____7123,uu____7124,uu____7125,uu____7126)
              ->
              ((let uu____7139 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____7139
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____7142 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____7142
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____7146 ->
              let uu____7154 =
                let uu____7155 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____7155  in
              if uu____7154 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____7159 ->
              let uu____7166 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____7166 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____7169 ->
              let uu____7175 =
                let uu____7176 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____7176  in
              if uu____7175 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____7180 ->
              let uu____7183 =
                let uu____7184 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____7184  in
              if uu____7183 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7188 ->
              let uu____7191 =
                let uu____7192 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____7192  in
              if uu____7191 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7196 ->
              let uu____7206 =
                let uu____7207 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____7207  in
              if uu____7206 then err'1 () else ()
          | uu____7211 -> ()))
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
                          let uu____7268 =
                            let uu____7271 =
                              let uu____7272 =
                                let uu____7277 =
                                  let uu____7278 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7278  in
                                (uu____7277, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7272  in
                            FStar_Syntax_Syntax.mk uu____7271  in
                          uu____7268 None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7304  ->
                                  match uu____7304 with
                                  | (x,imp) ->
                                      let uu____7311 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7311, imp)))
                           in
                        (FStar_Syntax_Syntax.mk_Tm_app inst_tc args) None p
                         in
                      let unrefined_arg_binder =
                        let uu____7317 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7317  in
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
                             let uu____7326 =
                               let uu____7327 =
                                 let uu____7328 =
                                   let uu____7329 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7330 =
                                     let uu____7331 =
                                       let uu____7332 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7332
                                        in
                                     [uu____7331]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7329
                                     uu____7330
                                    in
                                 uu____7328 None p  in
                               FStar_Syntax_Util.b2t uu____7327  in
                             FStar_Syntax_Util.refine x uu____7326  in
                           let uu____7337 =
                             let uu___147_7338 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___147_7338.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___147_7338.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7337)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7348 =
                          FStar_List.map
                            (fun uu____7358  ->
                               match uu____7358 with
                               | (x,uu____7365) ->
                                   (x, (Some FStar_Syntax_Syntax.imp_tag)))
                            tps
                           in
                        FStar_List.append uu____7348 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7389  ->
                                match uu____7389 with
                                | (x,uu____7396) ->
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
                             (let uu____7405 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Syntax_Const.prims_lid uu____7405)
                               ||
                               (let uu____7406 =
                                  let uu____7407 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7407.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7406)
                              in
                           let quals =
                             let uu____7410 =
                               let uu____7412 =
                                 let uu____7414 =
                                   only_decl &&
                                     ((FStar_All.pipe_left Prims.op_Negation
                                         env.FStar_TypeChecker_Env.is_iface)
                                        || env.FStar_TypeChecker_Env.admit)
                                    in
                                 if uu____7414
                                 then [FStar_Syntax_Syntax.Assumption]
                                 else []  in
                               let uu____7417 =
                                 FStar_List.filter
                                   (fun uu___107_7419  ->
                                      match uu___107_7419 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7420 -> false) iquals
                                  in
                               FStar_List.append uu____7412 uu____7417  in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then [FStar_Syntax_Syntax.Logic]
                                else [])) uu____7410
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7433 =
                                 let uu____7434 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7434  in
                               FStar_Syntax_Syntax.mk_Total uu____7433  in
                             let uu____7435 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7435
                              in
                           let decl =
                             FStar_Syntax_Syntax.Sig_declare_typ
                               (discriminator_name, uvs, t, quals,
                                 (FStar_Ident.range_of_lid discriminator_name))
                              in
                           (let uu____7439 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7439
                            then
                              let uu____7440 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7440
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
                                             fun uu____7468  ->
                                               match uu____7468 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7484 =
                                                       let uu____7487 =
                                                         let uu____7488 =
                                                           let uu____7493 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7493,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7488
                                                          in
                                                       pos uu____7487  in
                                                     (uu____7484, b)
                                                   else
                                                     (let uu____7497 =
                                                        let uu____7500 =
                                                          let uu____7501 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7501
                                                           in
                                                        pos uu____7500  in
                                                      (uu____7497, b))))
                                      in
                                   let pat_true =
                                     let uu____7513 =
                                       let uu____7516 =
                                         let uu____7517 =
                                           let uu____7525 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (Some fvq)
                                              in
                                           (uu____7525, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7517
                                          in
                                       pos uu____7516  in
                                     (uu____7513, None,
                                       FStar_Syntax_Const.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7547 =
                                       let uu____7550 =
                                         let uu____7551 =
                                           FStar_Syntax_Syntax.new_bv None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____7551
                                          in
                                       pos uu____7550  in
                                     (uu____7547, None,
                                       FStar_Syntax_Const.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (Prims.fst unrefined_arg_binder)
                                      in
                                   let uu____7560 =
                                     let uu____7563 =
                                       let uu____7564 =
                                         let uu____7580 =
                                           let uu____7582 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____7583 =
                                             let uu____7585 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____7585]  in
                                           uu____7582 :: uu____7583  in
                                         (arg_exp, uu____7580)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____7564
                                        in
                                     FStar_Syntax_Syntax.mk uu____7563  in
                                   uu____7560 None p)
                                 in
                              let dd =
                                let uu____7596 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____7596
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
                                let uu____7608 =
                                  let uu____7611 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd None
                                     in
                                  FStar_Util.Inr uu____7611  in
                                let uu____7612 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = uu____7608;
                                  FStar_Syntax_Syntax.lbunivs = uvs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    FStar_Syntax_Const.effect_Tot_lid;
                                  FStar_Syntax_Syntax.lbdef = uu____7612
                                }  in
                              let impl =
                                let uu____7616 =
                                  let uu____7625 =
                                    let uu____7627 =
                                      let uu____7628 =
                                        FStar_All.pipe_right
                                          lb.FStar_Syntax_Syntax.lbname
                                          FStar_Util.right
                                         in
                                      FStar_All.pipe_right uu____7628
                                        (fun fv  ->
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                       in
                                    [uu____7627]  in
                                  ((false, [lb]), p, uu____7625, quals, [])
                                   in
                                FStar_Syntax_Syntax.Sig_let uu____7616  in
                              (let uu____7644 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____7644
                               then
                                 let uu____7645 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____7645
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
                                fun uu____7665  ->
                                  match uu____7665 with
                                  | (a,uu____7669) ->
                                      let uu____7670 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____7670 with
                                       | (field_name,uu____7674) ->
                                           let field_proj_tm =
                                             let uu____7676 =
                                               let uu____7677 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____7677
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____7676 inst_univs
                                              in
                                           let proj =
                                             (FStar_Syntax_Syntax.mk_Tm_app
                                                field_proj_tm [arg]) None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____7693 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____7702  ->
                                    match uu____7702 with
                                    | (x,uu____7707) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____7709 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____7709 with
                                         | (field_name,uu____7714) ->
                                             let t =
                                               let uu____7716 =
                                                 let uu____7717 =
                                                   let uu____7718 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____7718
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____7717
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____7716
                                                in
                                             let only_decl =
                                               ((let uu____7720 =
                                                   FStar_TypeChecker_Env.current_module
                                                     env
                                                    in
                                                 FStar_Ident.lid_equals
                                                   FStar_Syntax_Const.prims_lid
                                                   uu____7720)
                                                  ||
                                                  (fvq <>
                                                     FStar_Syntax_Syntax.Data_ctor))
                                                 ||
                                                 (let uu____7721 =
                                                    let uu____7722 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____7722.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____7721)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____7732 =
                                                   FStar_List.filter
                                                     (fun uu___108_7734  ->
                                                        match uu___108_7734
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____7735 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____7732
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___109_7743  ->
                                                         match uu___109_7743
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                           
                                                           |FStar_Syntax_Syntax.Private
                                                            -> true
                                                         | uu____7744 ->
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
                                             ((let uu____7748 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____7748
                                               then
                                                 let uu____7749 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____7749
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
                                                           fun uu____7776  ->
                                                             match uu____7776
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
                                                                   let uu____7792
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____7792,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____7804
                                                                    =
                                                                    let uu____7807
                                                                    =
                                                                    let uu____7808
                                                                    =
                                                                    let uu____7813
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____7813,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____7808
                                                                     in
                                                                    pos
                                                                    uu____7807
                                                                     in
                                                                    (uu____7804,
                                                                    b))
                                                                   else
                                                                    (let uu____7817
                                                                    =
                                                                    let uu____7820
                                                                    =
                                                                    let uu____7821
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____7821
                                                                     in
                                                                    pos
                                                                    uu____7820
                                                                     in
                                                                    (uu____7817,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____7833 =
                                                     let uu____7836 =
                                                       let uu____7837 =
                                                         let uu____7845 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (Some fvq)
                                                            in
                                                         (uu____7845,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____7837
                                                        in
                                                     pos uu____7836  in
                                                   let uu____7851 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____7833, None,
                                                     uu____7851)
                                                    in
                                                 let body =
                                                   let uu____7862 =
                                                     let uu____7865 =
                                                       let uu____7866 =
                                                         let uu____7882 =
                                                           let uu____7884 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____7884]  in
                                                         (arg_exp,
                                                           uu____7882)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____7866
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____7865
                                                      in
                                                   uu____7862 None p1  in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body None
                                                    in
                                                 let dd =
                                                   let uu____7901 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____7901
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
                                                   let uu____7907 =
                                                     let uu____7910 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____7910
                                                      in
                                                   let uu____7911 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____7907;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Syntax_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____7911
                                                   }  in
                                                 let impl =
                                                   let uu____7915 =
                                                     let uu____7924 =
                                                       let uu____7926 =
                                                         let uu____7927 =
                                                           FStar_All.pipe_right
                                                             lb.FStar_Syntax_Syntax.lbname
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7927
                                                           (fun fv  ->
                                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                          in
                                                       [uu____7926]  in
                                                     ((false, [lb]), p1,
                                                       uu____7924, quals1,
                                                       [])
                                                      in
                                                   FStar_Syntax_Syntax.Sig_let
                                                     uu____7915
                                                    in
                                                 (let uu____7943 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____7943
                                                  then
                                                    let uu____7944 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____7944
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____7693 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,quals,uu____7975,r) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Syntax_Const.lexcons_lid)
              ->
              let uu____7981 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____7981 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____7994 = FStar_Syntax_Util.arrow_formals_comp t1
                      in
                   (match uu____7994 with
                    | (formals,uu____8002) ->
                        let uu____8009 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8022 =
                                   let uu____8023 =
                                     let uu____8024 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8024  in
                                   FStar_Ident.lid_equals typ_lid uu____8023
                                    in
                                 if uu____8022
                                 then
                                   match se1 with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8034,uvs',tps,typ0,uu____8038,constrs,uu____8040,uu____8041)
                                       ->
                                       Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8055 -> failwith "Impossible"
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
                        (match uu____8009 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____8097 =
                               FStar_Syntax_Util.arrow_formals_comp typ01  in
                             (match uu____8097 with
                              | (indices,uu____8105) ->
                                  let refine_domain =
                                    let uu____8113 =
                                      FStar_All.pipe_right quals
                                        (FStar_Util.for_some
                                           (fun uu___110_8115  ->
                                              match uu___110_8115 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____8116 -> true
                                              | uu____8121 -> false))
                                       in
                                    if uu____8113
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___111_8128 =
                                      match uu___111_8128 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____8130,fns) ->
                                          Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____8137 -> None  in
                                    let uu____8138 =
                                      FStar_Util.find_map quals
                                        filter_records
                                       in
                                    match uu____8138 with
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
                                    let uu____8146 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____8146 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____8177  ->
                                               fun uu____8178  ->
                                                 match (uu____8177,
                                                         uu____8178)
                                                 with
                                                 | ((x,uu____8188),(x',uu____8190))
                                                     ->
                                                     let uu____8195 =
                                                       let uu____8200 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____8200)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____8195) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____8201 -> []
  
let destruct_comp_term :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lid * FStar_Syntax_Syntax.universes)
  =
  fun m  ->
    let uu____8207 =
      let uu____8208 = FStar_Syntax_Subst.compress m  in
      uu____8208.FStar_Syntax_Syntax.n  in
    match uu____8207 with
    | FStar_Syntax_Syntax.Tm_uinst
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = uu____8214;
           FStar_Syntax_Syntax.pos = uu____8215;
           FStar_Syntax_Syntax.vars = uu____8216;_},univs1)
        ->
        let uu____8222 = FStar_Syntax_Syntax.lid_of_fv fv  in
        (uu____8222, univs1)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8224 = FStar_Syntax_Syntax.lid_of_fv fv  in
        (uu____8224, [])
    | uu____8226 -> failwith "Impossible"
  
let mlift_of_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_TypeChecker_Env.normal_comp_typ ->
        FStar_TypeChecker_Env.normal_comp_typ
  =
  fun env  ->
    fun sub1  ->
      let mlift nct =
        let fail uu____8243 =
          let uu____8244 =
            FStar_Util.format2
              "Invalid application of mlift, effect names differ : %s vs %s"
              (FStar_Ident.text_of_lid nct.FStar_TypeChecker_Env.nct_name)
              (FStar_Ident.text_of_lid
                 (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name)
             in
          FStar_All.pipe_left failwith uu____8244  in
        let uu____8245 =
          let skeleton =
            let uu____8255 =
              let uu____8258 =
                let uu____8261 =
                  let uu____8262 =
                    let uu____8270 =
                      FStar_Syntax_Syntax.mk_Total
                        FStar_TypeChecker_Common.t_unit
                       in
                    ((sub1.FStar_Syntax_Syntax.sub_eff_binders), uu____8270)
                     in
                  FStar_Syntax_Syntax.Tm_arrow uu____8262  in
                FStar_Syntax_Syntax.mk uu____8261  in
              uu____8258 None FStar_Range.dummyRange  in
            ((sub1.FStar_Syntax_Syntax.sub_eff_univs), uu____8255)  in
          let uu____8281 = FStar_TypeChecker_Env.inst_tscheme skeleton  in
          match uu____8281 with
          | (univ_meta_vars,skel) ->
              let uu____8290 =
                FStar_List.fold_right
                  (fun univ  ->
                     fun uu____8298  ->
                       match uu____8298 with
                       | (out,i) ->
                           (((FStar_Syntax_Syntax.UN (i, univ)) :: out),
                             (i + (Prims.parse_int "1")))) univ_meta_vars
                  ([],
                    (FStar_List.length
                       sub1.FStar_Syntax_Syntax.sub_eff_binders))
                 in
              (match uu____8290 with
               | (univ_meta_vars_subst,uu____8320) ->
                   let uu____8323 =
                     maybe_instantiate env FStar_Syntax_Syntax.tun skel  in
                   (match uu____8323 with
                    | (_term,_typ,_guard,index_meta_var_subst) ->
                        let effect_binders_opening =
                          let lift_to_bvar subst_elt uu____8350 =
                            match uu____8350 with
                            | (n1,l) ->
                                (match subst_elt with
                                 | FStar_Syntax_Syntax.NT (b,uu____8365) ->
                                     ((n1 + (Prims.parse_int "1")),
                                       ((FStar_Syntax_Syntax.DB (n1, b)) ::
                                       l))
                                 | uu____8371 ->
                                     failwith "Clearly impossible")
                             in
                          let uu____8375 =
                            FStar_List.fold_right lift_to_bvar
                              index_meta_var_subst
                              ((Prims.parse_int "0"), [])
                             in
                          FStar_All.pipe_left Prims.snd uu____8375  in
                        ((FStar_List.append univ_meta_vars_subst
                            index_meta_var_subst), effect_binders_opening)))
           in
        match uu____8245 with
        | (sigma,effect_binders_opening) ->
            ((let uu____8397 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Lift")
                 in
              if uu____8397
              then
                let uu____8398 =
                  FStar_Syntax_Print.subst_to_string effect_binders_opening
                   in
                let uu____8399 = FStar_Syntax_Print.subst_to_string sigma  in
                FStar_Util.print2 "Substitution used for lift : %s and %s\n"
                  uu____8398 uu____8399
              else ());
             (let dummy_wp =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun  in
              let formal_source =
                let ct =
                  let uu___148_8405 = sub1.FStar_Syntax_Syntax.sub_eff_source
                     in
                  {
                    FStar_Syntax_Syntax.comp_typ_name =
                      (uu___148_8405.FStar_Syntax_Syntax.comp_typ_name);
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___148_8405.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_args =
                      (FStar_List.append
                         (sub1.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.effect_args
                         [dummy_wp]);
                    FStar_Syntax_Syntax.flags =
                      (uu___148_8405.FStar_Syntax_Syntax.flags)
                  }  in
                let c =
                  let uu____8411 = FStar_Syntax_Syntax.mk_Comp ct  in
                  FStar_Syntax_Subst.subst_comp effect_binders_opening
                    uu____8411
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
              (let uu____8419 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "Lift")
                  in
               if uu____8419
               then
                 let uu____8420 =
                   FStar_Syntax_Print.comp_to_string formal_source  in
                 let uu____8421 =
                   FStar_Syntax_Print.comp_to_string actual_source  in
                 FStar_Util.print2 "trying to equate %s and %s\n" uu____8420
                   uu____8421
               else ());
              (let uu____8423 =
                 FStar_TypeChecker_Rel.sub_comp
                   (let uu___149_8425 = env  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___149_8425.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___149_8425.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___149_8425.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___149_8425.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___149_8425.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___149_8425.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___149_8425.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___149_8425.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___149_8425.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___149_8425.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___149_8425.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___149_8425.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___149_8425.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___149_8425.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___149_8425.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq = true;
                      FStar_TypeChecker_Env.is_iface =
                        (uu___149_8425.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___149_8425.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___149_8425.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___149_8425.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.type_of =
                        (uu___149_8425.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___149_8425.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___149_8425.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___149_8425.FStar_TypeChecker_Env.qname_and_index)
                    }) formal_source actual_source
                  in
               match uu____8423 with
               | None  -> fail ()
               | Some g -> FStar_TypeChecker_Rel.force_trivial_guard env g));
             (let target_nct =
                let target_wp =
                  let lift_wp =
                    let uu____8432 =
                      FStar_Util.must
                        sub1.FStar_Syntax_Syntax.sub_eff_lift_wp
                       in
                    FStar_Syntax_Subst.subst effect_binders_opening
                      uu____8432
                     in
                  let uu____8433 =
                    let uu____8434 = FStar_Syntax_Subst.subst sigma lift_wp
                       in
                    FStar_Syntax_Syntax.mk_Tm_app uu____8434
                      [nct.FStar_TypeChecker_Env.nct_wp]
                     in
                  uu____8433 None FStar_Range.dummyRange  in
                let target_comp_no_wp =
                  let c =
                    let uu____8441 =
                      FStar_Syntax_Syntax.mk_Comp
                        sub1.FStar_Syntax_Syntax.sub_eff_target
                       in
                    FStar_Syntax_Subst.subst_comp effect_binders_opening
                      uu____8441
                     in
                  let uu____8442 = FStar_Syntax_Subst.subst_comp sigma c  in
                  FStar_All.pipe_right uu____8442
                    FStar_Syntax_Util.comp_to_comp_typ
                   in
                let target_comp_typ =
                  let uu___150_8444 = target_comp_no_wp  in
                  let uu____8445 =
                    let uu____8451 =
                      let uu____8457 = FStar_Syntax_Syntax.as_arg target_wp
                         in
                      [uu____8457]  in
                    FStar_List.append
                      target_comp_no_wp.FStar_Syntax_Syntax.effect_args
                      uu____8451
                     in
                  {
                    FStar_Syntax_Syntax.comp_typ_name =
                      (uu___150_8444.FStar_Syntax_Syntax.comp_typ_name);
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___150_8444.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_args = uu____8445;
                    FStar_Syntax_Syntax.flags =
                      (uu___150_8444.FStar_Syntax_Syntax.flags)
                  }  in
                let c = FStar_Syntax_Syntax.mk_Comp target_comp_typ  in
                (let uu____8464 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "Lift")
                    in
                 if uu____8464
                 then
                   let uu____8465 = FStar_Syntax_Print.comp_to_string c  in
                   FStar_Util.print1 "Target comp type after lifting %s"
                     uu____8465
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
               let uu____8482 = e1.FStar_TypeChecker_Env.mlift nct  in
               e2.FStar_TypeChecker_Env.mlift uu____8482)
        }  in
      let edge =
        let uu____8488 = mlift_of_sub_eff env sub_eff  in
        {
          FStar_TypeChecker_Env.msource =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mtarget =
            ((sub_eff.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name);
          FStar_TypeChecker_Env.mlift = uu____8488
        }  in
      let id_edge l =
        {
          FStar_TypeChecker_Env.msource = l;
          FStar_TypeChecker_Env.mtarget = l;
          FStar_TypeChecker_Env.mlift = (fun nct  -> nct)
        }  in
      let print_mlift l =
        let arg =
          let uu____8512 =
            FStar_Ident.lid_of_path ["ARG"] FStar_Range.dummyRange  in
          FStar_Syntax_Syntax.lid_as_fv uu____8512
            FStar_Syntax_Syntax.Delta_constant None
           in
        let wp =
          let uu____8514 =
            FStar_Ident.lid_of_path ["WP"] FStar_Range.dummyRange  in
          FStar_Syntax_Syntax.lid_as_fv uu____8514
            FStar_Syntax_Syntax.Delta_constant None
           in
        let uu____8515 = l arg wp  in
        FStar_Syntax_Print.term_to_string uu____8515  in
      let order = edge ::
        ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.order)  in
      let ms =
        FStar_All.pipe_right
          (env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls
          (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____8533 =
        match uu____8533 with
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
                  let uu____8554 =
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
                                        (let uu____8566 =
                                           let uu____8571 =
                                             find_edge order1 (i, k)  in
                                           let uu____8573 =
                                             find_edge order1 (k, j)  in
                                           (uu____8571, uu____8573)  in
                                         match uu____8566 with
                                         | (Some e1,Some e2) ->
                                             let uu____8582 =
                                               compose_edges e1 e2  in
                                             [uu____8582]
                                         | uu____8583 -> [])))))
                     in
                  FStar_List.append order1 uu____8554) order)
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
              let uu____8595 =
                (FStar_Ident.lid_equals edge1.FStar_TypeChecker_Env.msource
                   FStar_Syntax_Const.effect_DIV_lid)
                  &&
                  (let uu____8596 =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       edge1.FStar_TypeChecker_Env.mtarget
                      in
                   FStar_All.pipe_right uu____8596
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____8595
              then
                let uu____8599 =
                  let uu____8600 =
                    let uu____8603 =
                      FStar_Util.format1
                        "Divergent computations cannot be included in an effect %s marked 'total'"
                        (edge1.FStar_TypeChecker_Env.mtarget).FStar_Ident.str
                       in
                    let uu____8604 = FStar_TypeChecker_Env.get_range env  in
                    (uu____8603, uu____8604)  in
                  FStar_Errors.Error uu____8600  in
                Prims.raise uu____8599
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
                                     let uu____8659 =
                                       let uu____8664 =
                                         find_edge order2 (i, k)  in
                                       let uu____8666 =
                                         find_edge order2 (j, k)  in
                                       (uu____8664, uu____8666)  in
                                     match uu____8659 with
                                     | (Some ik,Some jk) ->
                                         (match bopt with
                                          | None  -> Some (k, ik, jk)
                                          | Some (ub,uu____8689,uu____8690)
                                              ->
                                              let uu____8694 =
                                                (let uu____8695 =
                                                   find_edge order2 (k, ub)
                                                    in
                                                 FStar_Util.is_some
                                                   uu____8695)
                                                  &&
                                                  (let uu____8697 =
                                                     let uu____8698 =
                                                       find_edge order2
                                                         (ub, k)
                                                        in
                                                     FStar_Util.is_some
                                                       uu____8698
                                                      in
                                                   Prims.op_Negation
                                                     uu____8697)
                                                 in
                                              if uu____8694
                                              then Some (k, ik, jk)
                                              else bopt)
                                     | uu____8708 -> bopt) None)
                            in
                         match join_opt with
                         | None  -> []
                         | Some (k,e1,e2) ->
                             [(i, j, k, (e1.FStar_TypeChecker_Env.mlift),
                                (e2.FStar_TypeChecker_Env.mlift))]))))
          in
       let effects =
         let uu___151_8751 = env.FStar_TypeChecker_Env.effects  in
         {
           FStar_TypeChecker_Env.decls =
             (uu___151_8751.FStar_TypeChecker_Env.decls);
           FStar_TypeChecker_Env.order = order2;
           FStar_TypeChecker_Env.joins = joins
         }  in
       let uu___152_8752 = env  in
       {
         FStar_TypeChecker_Env.solver =
           (uu___152_8752.FStar_TypeChecker_Env.solver);
         FStar_TypeChecker_Env.range =
           (uu___152_8752.FStar_TypeChecker_Env.range);
         FStar_TypeChecker_Env.curmodule =
           (uu___152_8752.FStar_TypeChecker_Env.curmodule);
         FStar_TypeChecker_Env.gamma =
           (uu___152_8752.FStar_TypeChecker_Env.gamma);
         FStar_TypeChecker_Env.gamma_cache =
           (uu___152_8752.FStar_TypeChecker_Env.gamma_cache);
         FStar_TypeChecker_Env.modules =
           (uu___152_8752.FStar_TypeChecker_Env.modules);
         FStar_TypeChecker_Env.expected_typ =
           (uu___152_8752.FStar_TypeChecker_Env.expected_typ);
         FStar_TypeChecker_Env.sigtab =
           (uu___152_8752.FStar_TypeChecker_Env.sigtab);
         FStar_TypeChecker_Env.is_pattern =
           (uu___152_8752.FStar_TypeChecker_Env.is_pattern);
         FStar_TypeChecker_Env.instantiate_imp =
           (uu___152_8752.FStar_TypeChecker_Env.instantiate_imp);
         FStar_TypeChecker_Env.effects = effects;
         FStar_TypeChecker_Env.generalize =
           (uu___152_8752.FStar_TypeChecker_Env.generalize);
         FStar_TypeChecker_Env.letrecs =
           (uu___152_8752.FStar_TypeChecker_Env.letrecs);
         FStar_TypeChecker_Env.top_level =
           (uu___152_8752.FStar_TypeChecker_Env.top_level);
         FStar_TypeChecker_Env.check_uvars =
           (uu___152_8752.FStar_TypeChecker_Env.check_uvars);
         FStar_TypeChecker_Env.use_eq =
           (uu___152_8752.FStar_TypeChecker_Env.use_eq);
         FStar_TypeChecker_Env.is_iface =
           (uu___152_8752.FStar_TypeChecker_Env.is_iface);
         FStar_TypeChecker_Env.admit =
           (uu___152_8752.FStar_TypeChecker_Env.admit);
         FStar_TypeChecker_Env.lax =
           (uu___152_8752.FStar_TypeChecker_Env.lax);
         FStar_TypeChecker_Env.lax_universes =
           (uu___152_8752.FStar_TypeChecker_Env.lax_universes);
         FStar_TypeChecker_Env.type_of =
           (uu___152_8752.FStar_TypeChecker_Env.type_of);
         FStar_TypeChecker_Env.universe_of =
           (uu___152_8752.FStar_TypeChecker_Env.universe_of);
         FStar_TypeChecker_Env.use_bv_sorts =
           (uu___152_8752.FStar_TypeChecker_Env.use_bv_sorts);
         FStar_TypeChecker_Env.qname_and_index =
           (uu___152_8752.FStar_TypeChecker_Env.qname_and_index)
       })
  
let build_lattice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____8760) ->
          let uu___153_8761 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___153_8761.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___153_8761.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___153_8761.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___153_8761.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___153_8761.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___153_8761.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___153_8761.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___153_8761.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___153_8761.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___153_8761.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (let uu___154_8762 = env.FStar_TypeChecker_Env.effects  in
               {
                 FStar_TypeChecker_Env.decls = (ne ::
                   ((env.FStar_TypeChecker_Env.effects).FStar_TypeChecker_Env.decls));
                 FStar_TypeChecker_Env.order =
                   (uu___154_8762.FStar_TypeChecker_Env.order);
                 FStar_TypeChecker_Env.joins =
                   (uu___154_8762.FStar_TypeChecker_Env.joins)
               });
            FStar_TypeChecker_Env.generalize =
              (uu___153_8761.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___153_8761.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___153_8761.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___153_8761.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___153_8761.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___153_8761.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___153_8761.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___153_8761.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___153_8761.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___153_8761.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___153_8761.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___153_8761.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___153_8761.FStar_TypeChecker_Env.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect (sub1,uu____8764) ->
          extend_effect_lattice env sub1
      | uu____8765 -> env
  