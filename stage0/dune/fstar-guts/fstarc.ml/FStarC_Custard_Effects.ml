open Prims
let of_lid (env : FStarC_TypeChecker_Env.env) (l : FStarC_Ident.lident) :
  FStarC_Custard_Syntax.eff=
  let uu___ =
    if
      (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_GHOST_lid) ||
        (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Ghost_lid)
    then true
    else FStarC_TypeChecker_Env.is_erasable_effect env l in
  if uu___
  then FStarC_Custard_Syntax.E_Ghost
  else
    if
      ((FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_PURE_lid) ||
         (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Pure_lid))
        || (FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Tot_lid)
    then FStarC_Custard_Syntax.E_Pure
    else
      (let uu___1 = FStarC_TypeChecker_Util.effect_extraction_mode env l in
       match uu___1 with
       | FStarC_Syntax_Syntax.Extract_none reason ->
           FStarC_Errors.raise_error0
             FStarC_Errors_Codes.Error_CustardUnextractableEffect ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic
                [FStarC_Errors_Msg.text
                   (Prims.strcat "Custard cannot extract the effect "
                      (Prims.strcat (FStarC_Ident.string_of_lid l) "."));
                FStarC_Errors_Msg.text reason])
       | uu___2 -> FStarC_Custard_Syntax.E_Impure)
let head_is_impure_marker (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStarC_TypeChecker_Env.fv_has_attr env fv
             FStarC_Parser_Const.extract_as_impure_effect_lid
       | uu___3 -> false)
let impure_effect_result (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (hd, args) ->
      let uu___1 =
        let uu___2 = FStarC_Syntax_Util.un_uinst hd in
        uu___2.FStarC_Syntax_Syntax.n in
      (match uu___1 with
       | FStarC_Syntax_Syntax.Tm_fvar fv when
           FStarC_TypeChecker_Env.fv_has_attr env fv
             FStarC_Parser_Const.extract_as_impure_effect_lid
           ->
           (match args with
            | (a, uu___2)::uu___3 -> FStar_Pervasives_Native.Some a
            | [] -> FStar_Pervasives_Native.None)
       | uu___2 -> FStar_Pervasives_Native.None)
let is_erasable (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : Prims.bool=
  FStarC_TypeChecker_Env.is_erasable_effect env
    (FStarC_Syntax_Util.comp_effect_name c)
let result_typ (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.typ=
  let uu___ = is_erasable env c in
  if uu___
  then FStarC_Syntax_Syntax.t_unit
  else
    (let r = FStarC_Syntax_Util.comp_result c in
     let uu___1 = impure_effect_result env r in
     match uu___1 with
     | FStar_Pervasives_Native.Some a -> a
     | FStar_Pervasives_Native.None -> r)
let of_comp (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_Custard_Syntax.eff=
  let e = of_lid env (FStarC_Syntax_Util.comp_effect_name c) in
  let uu___ = head_is_impure_marker env (FStarC_Syntax_Util.comp_result c) in
  if uu___ then FStarC_Custard_Syntax.E_Impure else e
let is_reifiable (env : FStarC_TypeChecker_Env.env) (l : FStarC_Ident.lident)
  : Prims.bool=
  let uu___ = FStarC_TypeChecker_Util.effect_extraction_mode env l in
  match uu___ with
  | FStarC_Syntax_Syntax.Extract_reify -> true
  | uu___1 -> false
let reify_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.Inlining;
  FStarC_TypeChecker_Env.ForExtraction;
  FStarC_TypeChecker_Env.Unascribe]
let reify_comp (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_Syntax_Syntax.typ=
  FStarC_TypeChecker_Env.reify_comp env c FStarC_Syntax_Syntax.U_unknown
let rec maybe_reify (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) (l : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term=
  let uu___ = let uu___1 = is_reifiable env l in Prims.not uu___1 in
  if uu___
  then t
  else
    (let uu___1 =
       let uu___2 = FStarC_Syntax_Subst.compress t in
       uu___2.FStarC_Syntax_Syntax.n in
     match uu___1 with
     | FStarC_Syntax_Syntax.Tm_let
         { FStarC_Syntax_Syntax.lbs = (true, lbs);
           FStarC_Syntax_Syntax.body1 = body;_}
         ->
         let uu___2 = FStarC_Syntax_Subst.open_let_rec lbs body in
         (match uu___2 with
          | (lbs1, body1) ->
              let env' =
                FStarC_List.fold_left
                  (fun env1 lb ->
                     match lb.FStarC_Syntax_Syntax.lbname with
                     | FStar_Pervasives.Inl bv ->
                         FStarC_TypeChecker_Env.push_bv env1 bv
                     | FStar_Pervasives.Inr uu___3 -> env1) env lbs1 in
              let body2 = maybe_reify env' body1 l in
              let uu___3 = FStarC_Syntax_Subst.close_let_rec lbs1 body2 in
              (match uu___3 with
               | (lbs2, body3) ->
                   {
                     FStarC_Syntax_Syntax.n =
                       (FStarC_Syntax_Syntax.Tm_let
                          {
                            FStarC_Syntax_Syntax.lbs = (true, lbs2);
                            FStarC_Syntax_Syntax.body1 = body3
                          });
                     FStarC_Syntax_Syntax.pos = (t.FStarC_Syntax_Syntax.pos);
                     FStarC_Syntax_Syntax.hash_code =
                       (t.FStarC_Syntax_Syntax.hash_code)
                   }))
     | uu___2 ->
         let uu___3 =
           FStarC_Syntax_Util.mk_reify t (FStar_Pervasives_Native.Some l) in
         FStarC_TypeChecker_Util.norm_reify env reify_steps uu___3)
