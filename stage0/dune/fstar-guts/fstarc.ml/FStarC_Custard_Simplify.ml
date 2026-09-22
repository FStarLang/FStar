open Prims
let rec occurs (v : Prims.string) (x : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar w -> w = v
  | uu___ -> FStarC_Custard_Syntax.exists_child (occurs v) x
let delayed_operands (o : FStarC_Custard_Syntax.prim_op) : Prims.bool=
  match ((o.FStarC_Custard_Syntax.po_ty), (o.FStarC_Custard_Syntax.po_op))
  with
  | (FStar_Pervasives_Native.None, FStarC_Custard_Syntax.And) -> true
  | (FStar_Pervasives_Native.None, FStarC_Custard_Syntax.Or) -> true
  | uu___ -> false
let anf_expr (x0 : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let rec norm x =
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.ELet (v, t, e1, e2) ->
        let e11 = norm e1 in
        let e21 = norm e2 in
        {
          FStarC_Custard_Syntax.e =
            (FStarC_Custard_Syntax.ELet (v, t, e11, e21));
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | FStarC_Custard_Syntax.ESeq (a, b) ->
        let a1 = norm a in
        let b1 = norm b in
        {
          FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ESeq (a1, b1));
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | FStarC_Custard_Syntax.EFun (bs, b) ->
        let uu___ =
          let uu___1 = let uu___2 = norm b in (bs, uu___2) in
          FStarC_Custard_Syntax.EFun uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | FStarC_Custard_Syntax.EWhile (c, b) ->
        let c1 = norm c in
        let b1 = norm b in
        {
          FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EWhile (c1, b1));
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | FStarC_Custard_Syntax.EConst uu___ -> x
    | FStarC_Custard_Syntax.EVar uu___ -> x
    | FStarC_Custard_Syntax.EQual uu___ -> x
    | FStarC_Custard_Syntax.EAny -> x
    | FStarC_Custard_Syntax.EAbort uu___ -> x
    | uu___ ->
        let acc = FStarC_Effect.mk_ref [] in
        let atomic e =
          match e.FStarC_Custard_Syntax.e with
          | FStarC_Custard_Syntax.EQual uu___1 -> true
          | FStarC_Custard_Syntax.EVar uu___1 -> true
          | FStarC_Custard_Syntax.EConst uu___1 -> true
          | FStarC_Custard_Syntax.EAny -> true
          | uu___1 -> false in
        let operand e =
          let e1 = norm e in
          let uu___1 =
            if FStarC_Custard_Syntax.is_pure e1.FStarC_Custard_Syntax.eff
            then true
            else atomic e1 in
          if uu___1
          then e1
          else
            (let v =
               let uu___2 = FStarC_GenSym.next_id () in
               FStarC_Custard_Syntax.uniq "tmp" uu___2 in
             (let uu___3 =
                let uu___4 = FStarC_Effect.op_Bang acc in
                (v, (e1.FStarC_Custard_Syntax.ty), e1) :: uu___4 in
              FStarC_Effect.op_Colon_Equals acc uu___3);
             {
               FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar v);
               FStarC_Custard_Syntax.ty = (e1.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
             }) in
        let rec ops es =
          match es with
          | [] -> []
          | e::es1 -> let e1 = operand e in let rest = ops es1 in e1 :: rest in
        let rec fields fs =
          match fs with
          | [] -> []
          | (f, e)::fs1 ->
              let e1 = operand e in let rest = fields fs1 in (f, e1) :: rest in
        let body =
          match x.FStarC_Custard_Syntax.e with
          | FStarC_Custard_Syntax.EApp (h, es) ->
              let h1 = operand h in
              let es1 = ops es in
              {
                FStarC_Custard_Syntax.e =
                  (FStarC_Custard_Syntax.EApp (h1, es1));
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ECtor (n, es) ->
              let uu___1 =
                let uu___2 = let uu___3 = ops es in (n, uu___3) in
                FStarC_Custard_Syntax.ECtor uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ETuple es ->
              let uu___1 =
                let uu___2 = ops es in FStarC_Custard_Syntax.ETuple uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ERaise e1 ->
              let uu___1 =
                let uu___2 = norm e1 in FStarC_Custard_Syntax.ERaise uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ERecord (n, fs) ->
              let uu___1 =
                let uu___2 = let uu___3 = fields fs in (n, uu___3) in
                FStarC_Custard_Syntax.ERecord uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.EOp (o, es) ->
              if delayed_operands o
              then
                (match es with
                 | e::rest ->
                     let e1 = operand e in
                     let rest1 = FStarC_List.map norm rest in
                     {
                       FStarC_Custard_Syntax.e =
                         (FStarC_Custard_Syntax.EOp (o, (e1 :: rest1)));
                       FStarC_Custard_Syntax.ty =
                         (x.FStarC_Custard_Syntax.ty);
                       FStarC_Custard_Syntax.eff =
                         (x.FStarC_Custard_Syntax.eff)
                     }
                 | [] -> x)
              else
                (let uu___1 =
                   let uu___2 = let uu___3 = ops es in (o, uu___3) in
                   FStarC_Custard_Syntax.EOp uu___2 in
                 {
                   FStarC_Custard_Syntax.e = uu___1;
                   FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                   FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                 })
          | FStarC_Custard_Syntax.EProj (e, n, f) ->
              let uu___1 =
                let uu___2 = let uu___3 = operand e in (uu___3, n, f) in
                FStarC_Custard_Syntax.EProj uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.EDiscrim (e, n) ->
              let uu___1 =
                let uu___2 = let uu___3 = operand e in (uu___3, n) in
                FStarC_Custard_Syntax.EDiscrim uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ECast (e, c) ->
              let uu___1 =
                let uu___2 = let uu___3 = operand e in (uu___3, c) in
                FStarC_Custard_Syntax.ECast uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ECoerce (e, c) ->
              let uu___1 =
                let uu___2 = let uu___3 = operand e in (uu___3, c) in
                FStarC_Custard_Syntax.ECoerce uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.EIf (c, a, b) ->
              let c1 = operand c in
              let a1 = norm a in
              let b1 = norm b in
              {
                FStarC_Custard_Syntax.e =
                  (FStarC_Custard_Syntax.EIf (c1, a1, b1));
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.EMatch (s, brs) ->
              let s1 = operand s in
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStarC_List.map norm_branch brs in
                  (s1, uu___3) in
                FStarC_Custard_Syntax.EMatch uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | FStarC_Custard_Syntax.ETry (e, brs) ->
              let uu___1 =
                let uu___2 =
                  let uu___3 = norm e in
                  let uu___4 = FStarC_List.map norm_branch brs in
                  (uu___3, uu___4) in
                FStarC_Custard_Syntax.ETry uu___2 in
              {
                FStarC_Custard_Syntax.e = uu___1;
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              }
          | uu___1 -> x in
        let uu___1 = FStarC_Effect.op_Bang acc in
        FStarC_List.fold_left
          (fun acc1 uu___2 ->
             match uu___2 with
             | (v, t, e) ->
                 {
                   FStarC_Custard_Syntax.e =
                     (FStarC_Custard_Syntax.ELet (v, t, e, acc1));
                   FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                   FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                 }) body uu___1
  and norm_branch br =
    let uu___ = br in
    match uu___ with
    | (p, g, b) ->
        let uu___1 =
          match g with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some g1 ->
              let uu___2 = norm g1 in FStar_Pervasives_Native.Some uu___2 in
        let uu___2 = norm b in (p, uu___1, uu___2) in
  norm x0
let anf (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 = anf_expr dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
let bool_alt (p : FStarC_Custard_Syntax.pat)
  (body : FStarC_Custard_Syntax.expr) :
  Prims.bool FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  match p with
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CBool b) ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some b)
  | FStarC_Custard_Syntax.PWild ->
      FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
  | FStarC_Custard_Syntax.PVar v ->
      let uu___ = occurs v body in
      if uu___
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let as_if (brs : FStarC_Custard_Syntax.branch Prims.list) :
  (FStarC_Custard_Syntax.expr * FStarC_Custard_Syntax.expr)
    FStar_Pervasives_Native.option=
  match brs with
  | (p1, FStar_Pervasives_Native.None, b1)::(p2,
                                             FStar_Pervasives_Native.None,
                                             b2)::[]
      ->
      let uu___ =
        let uu___1 = bool_alt p1 b1 in
        let uu___2 = bool_alt p2 b2 in (uu___1, uu___2) in
      (match uu___ with
       | (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some c1),
          FStar_Pervasives_Native.Some alt2) ->
           let complementary =
             match alt2 with
             | FStar_Pervasives_Native.None -> true
             | FStar_Pervasives_Native.Some c2 -> c1 <> c2 in
           if Prims.not complementary
           then FStar_Pervasives_Native.None
           else
             if c1
             then FStar_Pervasives_Native.Some (b1, b2)
             else FStar_Pervasives_Native.Some (b2, b1)
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rec float_lets (x : FStarC_Custard_Syntax.expr)
  (e1 : FStarC_Custard_Syntax.expr)
  (k : FStarC_Custard_Syntax.expr -> FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  match e1.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet (w, t, a, b) ->
      let uu___ =
        let uu___1 = let uu___2 = float_lets x b k in (w, t, a, uu___2) in
        FStarC_Custard_Syntax.ELet uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ESeq (a, b) ->
      let uu___ =
        let uu___1 = let uu___2 = float_lets x b k in (a, uu___2) in
        FStarC_Custard_Syntax.ESeq uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
      }
  | uu___ -> k e1
type subst = FStarC_Custard_Syntax.expr FStarC_SMap.t
let rename (x : Prims.string) : Prims.string=
  let uu___ = FStarC_Custard_Syntax.base_name x in
  let uu___1 = FStarC_GenSym.next_id () in
  FStarC_Custard_Syntax.uniq uu___ uu___1
let rec sub (sm : subst) (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  let g = sub sm in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar v ->
      let uu___ = FStarC_SMap.try_find sm v in
      (match uu___ with
       | FStar_Pervasives_Native.Some e -> e
       | FStar_Pervasives_Native.None -> x)
  | FStarC_Custard_Syntax.EConst uu___ -> x
  | FStarC_Custard_Syntax.EQual uu___ -> x
  | FStarC_Custard_Syntax.EAny -> x
  | FStarC_Custard_Syntax.EAbort uu___ -> x
  | FStarC_Custard_Syntax.ELet (v, ty, e1, e2) ->
      let v' = rename v in
      let e11 = g e1 in
      (FStarC_SMap.add sm v
         {
           FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar v');
           FStarC_Custard_Syntax.ty = ty;
           FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
         };
       (let e21 = sub sm e2 in
        {
          FStarC_Custard_Syntax.e =
            (FStarC_Custard_Syntax.ELet (v', ty, e11, e21));
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }))
  | FStarC_Custard_Syntax.EFun (bs, b) ->
      let bs1 =
        FStarC_List.map
          (fun b1 ->
             let n = rename b1.FStarC_Custard_Syntax.b_name in
             FStarC_SMap.add sm b1.FStarC_Custard_Syntax.b_name
               {
                 FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar n);
                 FStarC_Custard_Syntax.ty = (b1.FStarC_Custard_Syntax.b_ty);
                 FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
               };
             {
               FStarC_Custard_Syntax.b_name = n;
               FStarC_Custard_Syntax.b_ty = (b1.FStarC_Custard_Syntax.b_ty)
             }) bs in
      let uu___ =
        let uu___1 = let uu___2 = sub sm b in (bs1, uu___2) in
        FStarC_Custard_Syntax.EFun uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EMatch (s, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g s in
          let uu___3 = FStarC_List.map (sub_branch sm) brs in
          (uu___2, uu___3) in
        FStarC_Custard_Syntax.EMatch uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ETry (a, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g a in
          let uu___3 = FStarC_List.map (sub_branch sm) brs in
          (uu___2, uu___3) in
        FStarC_Custard_Syntax.ETry uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
      }
  | uu___ -> FStarC_Custard_Syntax.map_children g x
and sub_branch (sm : subst) (br : FStarC_Custard_Syntax.branch) :
  FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, guard, b) ->
      let p1 = sub_pat sm p in
      let uu___1 =
        match guard with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some e ->
            let uu___2 = sub sm e in FStar_Pervasives_Native.Some uu___2 in
      let uu___2 = sub sm b in (p1, uu___1, uu___2)
and sub_pat (sm : subst) (p : FStarC_Custard_Syntax.pat) :
  FStarC_Custard_Syntax.pat=
  match p with
  | FStarC_Custard_Syntax.PWild -> p
  | FStarC_Custard_Syntax.PConst uu___ -> p
  | FStarC_Custard_Syntax.PVar v ->
      let v' = rename v in
      (FStarC_SMap.add sm v
         {
           FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar v');
           FStarC_Custard_Syntax.ty = FStarC_Custard_Syntax.TAny;
           FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
         };
       FStarC_Custard_Syntax.PVar v')
  | FStarC_Custard_Syntax.PCtor (n, ps) ->
      let uu___ = let uu___1 = FStarC_List.map (sub_pat sm) ps in (n, uu___1) in
      FStarC_Custard_Syntax.PCtor uu___
  | FStarC_Custard_Syntax.PRecord (n, fs) ->
      let uu___ =
        let uu___1 =
          FStarC_List.map
            (fun uu___2 ->
               match uu___2 with
               | (f, q) -> let uu___3 = sub_pat sm q in (f, uu___3)) fs in
        (n, uu___1) in
      FStarC_Custard_Syntax.PRecord uu___
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = FStarC_List.map (sub_pat sm) ps in
      FStarC_Custard_Syntax.PTuple uu___
  | FStarC_Custard_Syntax.POr ps ->
      let uu___ = FStarC_List.map (sub_pat sm) ps in
      FStarC_Custard_Syntax.POr uu___
let rec rename_var (v : Prims.string) (w : Prims.string)
  (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar u ->
      if u = v
      then
        {
          FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar w);
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
      else x
  | uu___ -> FStarC_Custard_Syntax.map_children (rename_var v w) x
let one_ctor : Prims.string Prims.list FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 100)
let ctor_family : Prims.string Prims.list FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 100)
let record_ctor_tables (prog : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t ->
           let put n fs =
             let uu___ = FStarC_Custard_Syntax.string_of_name n in
             let uu___1 = FStarC_List.map FStar_Pervasives_Native.fst fs in
             FStarC_SMap.add one_ctor uu___ uu___1 in
           (match t.FStarC_Custard_Syntax.dt_body with
            | FStarC_Custard_Syntax.TRecord fs ->
                put t.FStarC_Custard_Syntax.dt_name fs
            | FStarC_Custard_Syntax.TVariant cs ->
                let all =
                  FStarC_List.map
                    (fun uu___ ->
                       match uu___ with
                       | (cn, uu___1) ->
                           FStarC_Custard_Syntax.string_of_name cn) cs in
                (FStarC_List.iter
                   (fun uu___1 ->
                      match uu___1 with
                      | (cn, uu___2) ->
                          let uu___3 =
                            FStarC_Custard_Syntax.string_of_name cn in
                          FStarC_SMap.add ctor_family uu___3 all) cs;
                 (match cs with
                  | (cn, fs)::[] ->
                      (put t.FStarC_Custard_Syntax.dt_name fs; put cn fs)
                  | uu___1 -> ()))
            | uu___ -> ())
       | uu___ -> ()) prog
let fields_of (n : FStarC_Custard_Syntax.name) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  let uu___ = FStarC_Custard_Syntax.string_of_name n in
  FStarC_SMap.try_find one_ctor uu___
let same_vars (ps : FStarC_Custard_Syntax.pat Prims.list)
  (es : FStarC_Custard_Syntax.expr Prims.list) : Prims.bool=
  if (FStarC_List.length ps) = (FStarC_List.length es)
  then
    FStarC_List.for_all
      (fun uu___ ->
         match uu___ with
         | (q, e) ->
             (match (q, (e.FStarC_Custard_Syntax.e)) with
              | (FStarC_Custard_Syntax.PVar a, FStarC_Custard_Syntax.EVar b)
                  -> a = b
              | uu___1 -> false)) (FStarC_List.zip ps es)
  else false
let id_branch (s : FStarC_Custard_Syntax.expr)
  (br : FStarC_Custard_Syntax.branch) :
  Prims.string FStar_Pervasives_Native.option=
  let scrut_var w =
    match s.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EVar v -> v = w
    | uu___ -> false in
  match br with
  | (p, FStar_Pervasives_Native.None, body) ->
      (match (p, (body.FStarC_Custard_Syntax.e)) with
       | (FStarC_Custard_Syntax.PCtor (cn, ps), FStarC_Custard_Syntax.ECtor
          (dn, es)) when
           let uu___ =
             let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
             let uu___2 = FStarC_Custard_Syntax.string_of_name dn in
             uu___1 = uu___2 in
           if uu___ then same_vars ps es else false ->
           let uu___ = FStarC_Custard_Syntax.string_of_name cn in
           FStar_Pervasives_Native.Some uu___
       | (FStarC_Custard_Syntax.PRecord (tn, fps),
          FStarC_Custard_Syntax.ERecord (rn, fes)) when
           let uu___ =
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStarC_Custard_Syntax.string_of_name tn in
                 let uu___4 = FStarC_Custard_Syntax.string_of_name rn in
                 uu___3 = uu___4 in
               if uu___2
               then (FStarC_List.length fps) = (FStarC_List.length fes)
               else false in
             if uu___1
             then
               FStarC_List.for_all
                 (fun uu___2 ->
                    match uu___2 with | ((f, uu___3), (g, uu___4)) -> f = g)
                 (FStarC_List.zip fps fes)
             else false in
           if uu___
           then
             let uu___1 = FStarC_List.map FStar_Pervasives_Native.snd fps in
             let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd fes in
             same_vars uu___1 uu___2
           else false ->
           let uu___ = FStarC_Custard_Syntax.string_of_name tn in
           FStar_Pervasives_Native.Some uu___
       | (FStarC_Custard_Syntax.PWild, FStarC_Custard_Syntax.EVar w) when
           scrut_var w -> FStar_Pervasives_Native.Some ""
       | (FStarC_Custard_Syntax.PVar u, FStarC_Custard_Syntax.EVar w) when
           if u = w then true else scrut_var w ->
           FStar_Pervasives_Native.Some ""
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let covers_type (cs : Prims.string Prims.list) : Prims.bool=
  let uu___ = FStarC_List.existsb (fun c -> c = "") cs in
  if uu___
  then true
  else
    (match cs with
     | [] -> false
     | c0::uu___1 ->
         let uu___2 = FStarC_SMap.try_find ctor_family c0 in
         (match uu___2 with
          | FStar_Pervasives_Native.Some all ->
              FStarC_List.for_all
                (fun c -> FStarC_List.existsb (fun d -> d = c) cs) all
          | FStar_Pervasives_Native.None ->
              (FStarC_List.length cs) = Prims.int_one))
let rebuild_id (s : FStarC_Custard_Syntax.expr)
  (brs : FStarC_Custard_Syntax.branch Prims.list) :
  FStarC_Custard_Syntax.expr FStar_Pervasives_Native.option=
  let rec go bs acc =
    match bs with
    | [] -> FStar_Pervasives_Native.Some acc
    | b::rest ->
        let uu___ = id_branch s b in
        (match uu___ with
         | FStar_Pervasives_Native.Some c -> go rest (c :: acc)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None) in
  let uu___ = go brs [] in
  match uu___ with
  | FStar_Pervasives_Native.Some cs ->
      let uu___1 = covers_type cs in
      if uu___1
      then FStar_Pervasives_Native.Some s
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let proj_spine (n : FStarC_Custard_Syntax.name)
  (fs : Prims.string Prims.list) (es : FStarC_Custard_Syntax.expr Prims.list)
  : FStarC_Custard_Syntax.expr FStar_Pervasives_Native.option=
  if
    (match fs with | [] -> true | uu___ -> false) ||
      ((FStarC_List.length fs) <> (FStarC_List.length es))
  then FStar_Pervasives_Native.None
  else
    (let base = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
     let ok =
       FStarC_List.for_all
         (fun uu___ ->
            match uu___ with
            | (f, e) ->
                (match e.FStarC_Custard_Syntax.e with
                 | FStarC_Custard_Syntax.EProj (s, pn, g) ->
                     let uu___1 =
                       if g = f
                       then
                         let uu___2 = FStarC_Custard_Syntax.string_of_name pn in
                         let uu___3 = FStarC_Custard_Syntax.string_of_name n in
                         uu___2 = uu___3
                       else false in
                     if uu___1
                     then
                       let uu___2 =
                         let uu___3 = FStarC_Effect.op_Bang base in
                         ((s.FStarC_Custard_Syntax.e), uu___3) in
                       (match uu___2 with
                        | (FStarC_Custard_Syntax.EVar v,
                           FStar_Pervasives_Native.None) ->
                            (FStarC_Effect.op_Colon_Equals base
                               (FStar_Pervasives_Native.Some s);
                             true)
                        | (FStarC_Custard_Syntax.EVar v,
                           FStar_Pervasives_Native.Some b) ->
                            (match b.FStarC_Custard_Syntax.e with
                             | FStarC_Custard_Syntax.EVar w -> v = w
                             | uu___3 -> false)
                        | uu___3 -> false)
                     else false
                 | uu___1 -> false)) (FStarC_List.zip fs es) in
     if ok then FStarC_Effect.op_Bang base else FStar_Pervasives_Native.None)
let rebuild_proj_id (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr FStar_Pervasives_Native.option=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ECtor (n, es) ->
      let uu___ = fields_of n in
      (match uu___ with
       | FStar_Pervasives_Native.Some fs -> proj_spine n fs es
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStarC_Custard_Syntax.ERecord (n, fs) ->
      let uu___ = FStarC_List.map FStar_Pervasives_Native.fst fs in
      let uu___1 = FStarC_List.map FStar_Pervasives_Native.snd fs in
      proj_spine n uu___ uu___1
  | FStarC_Custard_Syntax.ETuple es ->
      (match es with
       | [] -> FStar_Pervasives_Native.None
       | e0::uu___ ->
           (match e0.FStarC_Custard_Syntax.e with
            | FStarC_Custard_Syntax.EProj (uu___1, n, uu___2) ->
                let uu___3 =
                  FStarC_List.mapi
                    (fun i uu___4 ->
                       Prims.strcat "_"
                         (Prims.string_of_int (i + Prims.int_one))) es in
                proj_spine n uu___3 es
            | uu___1 -> FStar_Pervasives_Native.None))
  | uu___ -> FStar_Pervasives_Native.None
let rec simpl (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet (v, ty, e1, e2) ->
      let e11 = simpl e1 in
      let e21 = simpl e2 in
      float_lets x e11
        (fun e12 ->
           if
             match e21.FStarC_Custard_Syntax.e with
             | FStarC_Custard_Syntax.EVar w -> w = v
             | uu___ -> false
           then e12
           else
             if
               (match e12.FStarC_Custard_Syntax.e with
                | FStarC_Custard_Syntax.EVar w -> w <> v
                | uu___ -> false)
             then
               (let w =
                  match e12.FStarC_Custard_Syntax.e with
                  | FStarC_Custard_Syntax.EVar w1 -> w1
                  | uu___ -> v in
                rename_var v w e21)
             else
               (let uu___ = occurs v e21 in
                if uu___
                then
                  {
                    FStarC_Custard_Syntax.e =
                      (FStarC_Custard_Syntax.ELet (v, ty, e12, e21));
                    FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                  }
                else
                  (let uu___1 = FStarC_Custard_Syntax.is_droppable e12 in
                   if uu___1
                   then e21
                   else
                     {
                       FStarC_Custard_Syntax.e =
                         (FStarC_Custard_Syntax.ESeq (e12, e21));
                       FStarC_Custard_Syntax.ty =
                         (x.FStarC_Custard_Syntax.ty);
                       FStarC_Custard_Syntax.eff =
                         (x.FStarC_Custard_Syntax.eff)
                     })))
  | FStarC_Custard_Syntax.ESeq (e1, e2) ->
      let e11 = simpl e1 in
      let e21 = simpl e2 in
      float_lets x e11
        (fun e12 ->
           let uu___ = FStarC_Custard_Syntax.is_droppable e12 in
           if uu___
           then e21
           else
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.ESeq (e12, e21));
               FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
             })
  | FStarC_Custard_Syntax.EMatch (s, brs) ->
      let s1 = simpl s in
      let brs1 = FStarC_List.map simpl_branch brs in
      let uu___ = rebuild_id s1 brs1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some r -> r
       | FStar_Pervasives_Native.None ->
           let uu___1 = as_if brs1 in
           (match uu___1 with
            | FStar_Pervasives_Native.Some (t, f) ->
                {
                  FStarC_Custard_Syntax.e =
                    (FStarC_Custard_Syntax.EIf (s1, t, f));
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                }
            | FStar_Pervasives_Native.None ->
                {
                  FStarC_Custard_Syntax.e =
                    (FStarC_Custard_Syntax.EMatch (s1, brs1));
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                }))
  | FStarC_Custard_Syntax.ECtor (n, es) ->
      let r =
        let uu___ =
          let uu___1 = let uu___2 = FStarC_List.map simpl es in (n, uu___2) in
          FStarC_Custard_Syntax.ECtor uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        } in
      let uu___ = rebuild_proj_id r in
      (match uu___ with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None -> r)
  | FStarC_Custard_Syntax.ETuple es ->
      let r =
        let uu___ =
          let uu___1 = FStarC_List.map simpl es in
          FStarC_Custard_Syntax.ETuple uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        } in
      let uu___ = rebuild_proj_id r in
      (match uu___ with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None -> r)
  | FStarC_Custard_Syntax.ERecord (n, fs) ->
      let r =
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (f, e) -> let uu___4 = simpl e in (f, uu___4)) fs in
            (n, uu___2) in
          FStarC_Custard_Syntax.ERecord uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        } in
      let uu___ = rebuild_proj_id r in
      (match uu___ with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None -> r)
  | FStarC_Custard_Syntax.ECast (e1, c) ->
      let e11 = simpl e1 in
      (match ((e11.FStarC_Custard_Syntax.e), c) with
       | (FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt
          (n, uu___, uu___1)), FStarC_Custard_Syntax.TFloat fw) ->
           (match FStarC_Custard_Syntax.float_lit_of_int fw n with
            | FStar_Pervasives_Native.Some f ->
                {
                  FStarC_Custard_Syntax.e =
                    (FStarC_Custard_Syntax.EConst
                       (FStarC_Custard_Syntax.CFloat (f, fw)));
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                }
            | FStar_Pervasives_Native.None ->
                {
                  FStarC_Custard_Syntax.e =
                    (FStarC_Custard_Syntax.ECast (e11, c));
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                })
       | uu___ ->
           {
             FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ECast (e11, c));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | uu___ -> FStarC_Custard_Syntax.map_children simpl x
and simpl_branch (br : FStarC_Custard_Syntax.branch) :
  FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 =
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g1 ->
            let uu___2 = simpl g1 in FStar_Pervasives_Native.Some uu___2 in
      let uu___2 = simpl b in (p, uu___1, uu___2)
let imax (a : Prims.int) (b : Prims.int) : Prims.int= if a >= b then a else b
let imin (a : Prims.int) (b : Prims.int) : Prims.int= if a <= b then a else b
let rec count (v : Prims.string) (x : FStarC_Custard_Syntax.expr) :
  Prims.int=
  let uu___ = occurs v x in
  if uu___
  then
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EVar uu___1 -> Prims.int_one
    | FStarC_Custard_Syntax.EMatch (s, brs) ->
        let uu___1 =
          let uu___2 = count v s in
          let uu___3 =
            FStarC_List.fold_left
              (fun acc uu___4 ->
                 match uu___4 with
                 | (uu___5, g, b) ->
                     let uu___6 =
                       let uu___7 = count v b in
                       let uu___8 =
                         match g with
                         | FStar_Pervasives_Native.None -> Prims.int_zero
                         | FStar_Pervasives_Native.Some g1 -> count v g1 in
                       uu___7 + uu___8 in
                     imax acc uu___6) Prims.int_zero brs in
          uu___2 + uu___3 in
        imin (Prims.of_int 2) uu___1
    | FStarC_Custard_Syntax.EIf (c, a, b) ->
        let uu___1 =
          let uu___2 = count v c in
          let uu___3 =
            let uu___4 = count v a in
            let uu___5 = count v b in imax uu___4 uu___5 in
          uu___2 + uu___3 in
        imin (Prims.of_int 2) uu___1
    | FStarC_Custard_Syntax.ETry (a, brs) ->
        let uu___1 =
          let uu___2 = count v a in
          let uu___3 =
            FStarC_List.fold_left
              (fun acc uu___4 ->
                 match uu___4 with
                 | (uu___5, uu___6, b) ->
                     let uu___7 = count v b in imax acc uu___7)
              Prims.int_zero brs in
          uu___2 + uu___3 in
        imin (Prims.of_int 2) uu___1
    | uu___1 ->
        FStarC_Custard_Syntax.fold_children
          (fun acc e ->
             let uu___2 = let uu___3 = count v e in acc + uu___3 in
             imin (Prims.of_int 2) uu___2) Prims.int_zero x
  else Prims.int_zero
let is_atomic (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar uu___ -> true
  | FStarC_Custard_Syntax.EConst uu___ -> true
  | FStarC_Custard_Syntax.EQual uu___ -> true
  | uu___ -> false
let inline_call (bs : FStarC_Custard_Syntax.binder Prims.list)
  (body : FStarC_Custard_Syntax.expr)
  (args : FStarC_Custard_Syntax.expr Prims.list)
  (at : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let sm = FStarC_SMap.create (Prims.of_int 10) in
  let lets =
    FStarC_List.collect
      (fun uu___ ->
         match uu___ with
         | (b, a) ->
             let uu___1 =
               if is_atomic a
               then true
               else
                 if FStarC_Custard_Syntax.is_pure a.FStarC_Custard_Syntax.eff
                 then
                   (let uu___2 = count b.FStarC_Custard_Syntax.b_name body in
                    uu___2 <= Prims.int_one)
                 else false in
             if uu___1
             then (FStarC_SMap.add sm b.FStarC_Custard_Syntax.b_name a; [])
             else
               (let v = rename b.FStarC_Custard_Syntax.b_name in
                FStarC_SMap.add sm b.FStarC_Custard_Syntax.b_name
                  {
                    FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar v);
                    FStarC_Custard_Syntax.ty = (a.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff = (a.FStarC_Custard_Syntax.eff)
                  };
                [(v, (b.FStarC_Custard_Syntax.b_ty), a)]))
      (FStarC_List.zip bs args) in
  let r = sub sm body in
  let r1 =
    {
      FStarC_Custard_Syntax.e = (r.FStarC_Custard_Syntax.e);
      FStarC_Custard_Syntax.ty = (at.FStarC_Custard_Syntax.ty);
      FStarC_Custard_Syntax.eff = (at.FStarC_Custard_Syntax.eff)
    } in
  FStarC_List.fold_right
    (fun uu___ acc ->
       match uu___ with
       | (v, ty, a) ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.ELet (v, ty, a, acc));
             FStarC_Custard_Syntax.ty = (acc.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (acc.FStarC_Custard_Syntax.eff)
           }) lets r1
let beta (bs : FStarC_Custard_Syntax.binder Prims.list)
  (body : FStarC_Custard_Syntax.expr)
  (args : FStarC_Custard_Syntax.expr Prims.list)
  (at : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let n = FStarC_List.length bs in
  if (FStarC_List.length args) < n
  then at
  else
    (let uu___ = FStarC_List.splitAt n args in
     match uu___ with
     | (given, extra) ->
         let r = inline_call bs body given at in
         (match extra with
          | [] -> r
          | uu___1 ->
              {
                FStarC_Custard_Syntax.e =
                  (FStarC_Custard_Syntax.EApp (r, extra));
                FStarC_Custard_Syntax.ty = (at.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (at.FStarC_Custard_Syntax.eff)
              }))
let rec match_pat (p : FStarC_Custard_Syntax.pat)
  (e : FStarC_Custard_Syntax.expr) :
  (Prims.string * FStarC_Custard_Syntax.expr) Prims.list
    FStar_Pervasives_Native.option=
  match (p, (e.FStarC_Custard_Syntax.e)) with
  | (FStarC_Custard_Syntax.PWild, uu___) -> FStar_Pervasives_Native.Some []
  | (FStarC_Custard_Syntax.PVar v, uu___) ->
      FStar_Pervasives_Native.Some [(v, e)]
  | (FStarC_Custard_Syntax.PCtor (n, ps), FStarC_Custard_Syntax.ECtor
     (m, es)) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        let uu___2 = FStarC_Custard_Syntax.string_of_name m in
        uu___1 = uu___2 in
      if uu___ then match_pats ps es else FStar_Pervasives_Native.None
  | (FStarC_Custard_Syntax.PRecord (uu___, fs), FStarC_Custard_Syntax.ERecord
     (uu___1, es)) ->
      FStarC_List.fold_left
        (fun acc uu___2 ->
           match uu___2 with
           | (f, q) ->
               let uu___3 =
                 let uu___4 =
                   FStarC_List.tryFind
                     (fun uu___5 -> match uu___5 with | (g, uu___6) -> g = f)
                     es in
                 (acc, uu___4) in
               (match uu___3 with
                | (FStar_Pervasives_Native.Some bs,
                   FStar_Pervasives_Native.Some (uu___4, e1)) ->
                    let uu___5 = match_pat q e1 in
                    (match uu___5 with
                     | FStar_Pervasives_Native.Some bs' ->
                         FStar_Pervasives_Native.Some
                           (FStarC_List.op_At bs bs')
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None)
                | uu___4 -> FStar_Pervasives_Native.None))
        (FStar_Pervasives_Native.Some []) fs
  | (FStarC_Custard_Syntax.PTuple ps, FStarC_Custard_Syntax.ETuple es) ->
      match_pats ps es
  | (FStarC_Custard_Syntax.PConst c1, FStarC_Custard_Syntax.EConst c2) ->
      if FStarC_Custard_Syntax.const_eq c1 c2
      then FStar_Pervasives_Native.Some []
      else FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
and match_pats (ps : FStarC_Custard_Syntax.pat Prims.list)
  (es : FStarC_Custard_Syntax.expr Prims.list) :
  (Prims.string * FStarC_Custard_Syntax.expr) Prims.list
    FStar_Pervasives_Native.option=
  match (ps, es) with
  | ([], []) -> FStar_Pervasives_Native.Some []
  | (p::ps1, e::es1) ->
      let uu___ =
        let uu___1 = match_pat p e in
        let uu___2 = match_pats ps1 es1 in (uu___1, uu___2) in
      (match uu___ with
       | (FStar_Pervasives_Native.Some l1, FStar_Pervasives_Native.Some l2)
           -> FStar_Pervasives_Native.Some (FStarC_List.op_At l1 l2)
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rec ctor_args_pure (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ECtor (uu___, es) ->
      FStarC_List.for_all
        (fun a -> FStarC_Custard_Syntax.is_pure a.FStarC_Custard_Syntax.eff)
        es
  | FStarC_Custard_Syntax.ETuple es ->
      FStarC_List.for_all
        (fun a -> FStarC_Custard_Syntax.is_pure a.FStarC_Custard_Syntax.eff)
        es
  | uu___ -> false
let rec iota (brs : FStarC_Custard_Syntax.branch Prims.list)
  (scrut : FStarC_Custard_Syntax.expr) (at : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  match brs with
  | [] -> at
  | (p, FStar_Pervasives_Native.None, body)::brs1 ->
      let uu___ = match_pat p scrut in
      (match uu___ with
       | FStar_Pervasives_Native.None -> at
       | FStar_Pervasives_Native.Some bnds ->
           let uu___1 =
             FStarC_List.map
               (fun uu___2 ->
                  match uu___2 with
                  | (v, a) ->
                      {
                        FStarC_Custard_Syntax.b_name = v;
                        FStarC_Custard_Syntax.b_ty =
                          (a.FStarC_Custard_Syntax.ty)
                      }) bnds in
           let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd bnds in
           inline_call uu___1 body uu___2 at)
  | uu___ -> at
let rec called_only (v : Prims.string) (x : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  let uu___ = let uu___1 = occurs v x in Prims.not uu___1 in
  if uu___
  then true
  else
    (match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.EVar uu___1 -> false
     | FStarC_Custard_Syntax.EApp (h, es) ->
         (match h.FStarC_Custard_Syntax.e with
          | FStarC_Custard_Syntax.EVar w ->
              if w = v then called_only_list v es else false
          | uu___1 ->
              let uu___2 = called_only v h in
              if uu___2 then called_only_list v es else false)
     | uu___1 -> FStarC_Custard_Syntax.for_all_children (called_only v) x)
and called_only_list (v : Prims.string)
  (es : FStarC_Custard_Syntax.expr Prims.list) : Prims.bool=
  FStarC_List.for_all (called_only v) es
let forwarders : (Prims.int * Prims.int) FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let forwarder_table (prog : FStarC_Custard_Syntax.program) :
  (Prims.int * Prims.int) FStarC_SMap.t=
  let t = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l when
           if
             (match l.FStarC_Custard_Syntax.dl_binders with
              | hd::tl -> true
              | uu___1 -> false) &&
               (FStarC_Custard_Syntax.is_pure l.FStarC_Custard_Syntax.dl_eff)
           then
             let uu___1 =
               FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Rec
                 l.FStarC_Custard_Syntax.dl_flags in
             Prims.not uu___1
           else false ->
           (match (l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e
            with
            | FStarC_Custard_Syntax.EVar v ->
                let n = FStarC_List.length l.FStarC_Custard_Syntax.dl_binders in
                let found =
                  FStarC_List.fold_left
                    (fun uu___1 b ->
                       match uu___1 with
                       | (acc, k) ->
                           ((if
                               (b.FStarC_Custard_Syntax.b_name = v) &&
                                 (acc < Prims.int_zero)
                             then k
                             else acc), (k + Prims.int_one)))
                    ((Prims.of_int (-1)), Prims.int_zero)
                    l.FStarC_Custard_Syntax.dl_binders in
                let found1 = FStar_Pervasives_Native.fst found in
                if found1 >= Prims.int_zero
                then
                  let uu___1 =
                    FStarC_Custard_Syntax.string_of_name
                      l.FStarC_Custard_Syntax.dl_name in
                  FStarC_SMap.add t uu___1 (n, found1)
                else ()
            | uu___1 -> ())
       | uu___1 -> ()) prog;
  t
let rec reeval (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  if FStarC_Custard_Syntax.is_pure e.FStarC_Custard_Syntax.eff
  then
    match e.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EVar uu___ -> true
    | FStarC_Custard_Syntax.EConst uu___ -> true
    | FStarC_Custard_Syntax.EQual uu___ -> true
    | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> reeval a
    | FStarC_Custard_Syntax.EDiscrim (a, uu___) -> reeval a
    | FStarC_Custard_Syntax.ECast (a, uu___) -> reeval a
    | FStarC_Custard_Syntax.ECoerce (a, uu___) -> reeval a
    | FStarC_Custard_Syntax.EOp (uu___, es) -> FStarC_List.for_all reeval es
    | FStarC_Custard_Syntax.ECtor (uu___, es) ->
        FStarC_List.for_all reeval es
    | FStarC_Custard_Syntax.ETuple es -> FStarC_List.for_all reeval es
    | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
        FStarC_List.for_all
          (fun uu___1 -> match uu___1 with | (uu___2, e1) -> reeval e1) fs
    | uu___ -> false
  else false
let rec destructed_only (v : Prims.string) (x : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  let g = destructed_only v in
  let scrut s =
    match s.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EVar w -> w = v
    | uu___ -> g s in
  let brs_ok brs =
    FStarC_List.for_all
      (fun b ->
         let uu___ = b in
         match uu___ with
         | (uu___1, gd, bd) ->
             let uu___2 =
               match gd with
               | FStar_Pervasives_Native.Some gd1 -> g gd1
               | FStar_Pervasives_Native.None -> true in
             if uu___2 then g bd else false) brs in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar w -> w <> v
  | FStarC_Custard_Syntax.EProj (e1, uu___, uu___1) ->
      (match e1.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EVar w -> if w = v then true else g e1
       | uu___2 -> g e1)
  | FStarC_Custard_Syntax.EMatch (s, brs) ->
      let uu___ = scrut s in if uu___ then brs_ok brs else false
  | FStarC_Custard_Syntax.ETry (s, brs) ->
      let uu___ = g s in if uu___ then brs_ok brs else false
  | uu___ -> FStarC_Custard_Syntax.for_all_children g x
let rec reduce (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EApp (h, args) ->
      let h1 = reduce h in
      let args1 = FStarC_List.map reduce args in
      (match h1.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EFun (bs, body) when
           (FStarC_List.length bs) <= (FStarC_List.length args1) ->
           let uu___ =
             beta bs body args1
               {
                 FStarC_Custard_Syntax.e =
                   (FStarC_Custard_Syntax.EApp (h1, args1));
                 FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                 FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
               } in
           reduce uu___
       | FStarC_Custard_Syntax.EQual (n, uu___) when
           let uu___1 =
             let uu___2 = FStarC_Effect.op_Bang forwarders in
             let uu___3 = FStarC_Custard_Syntax.string_of_name n in
             FStarC_SMap.try_find uu___2 uu___3 in
           match uu___1 with
           | FStar_Pervasives_Native.Some (a, uu___2) ->
               if a = (FStarC_List.length args1)
               then
                 FStarC_List.for_all
                   (fun e ->
                      FStarC_Custard_Syntax.is_pure
                        e.FStarC_Custard_Syntax.eff) args1
               else false
           | FStar_Pervasives_Native.None -> false ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Effect.op_Bang forwarders in
               let uu___4 = FStarC_Custard_Syntax.string_of_name n in
               FStarC_SMap.try_find uu___3 uu___4 in
             match uu___2 with | FStar_Pervasives_Native.Some v -> v in
           (match uu___1 with
            | (uu___2, i) ->
                let arg = FStarC_List.nth args1 i in
                {
                  FStarC_Custard_Syntax.e = (arg.FStarC_Custard_Syntax.e);
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (arg.FStarC_Custard_Syntax.eff)
                })
       | uu___ ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EApp (h1, args1));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.EMatch (scrut, brs) ->
      let scrut1 = reduce scrut in
      let uu___ = ctor_args_pure scrut1 in
      if uu___
      then
        let r =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_List.map reduce_branch brs in
                (scrut1, uu___4) in
              FStarC_Custard_Syntax.EMatch uu___3 in
            {
              FStarC_Custard_Syntax.e = uu___2;
              FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
              FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
            } in
          iota brs scrut1 uu___1 in
        (match r.FStarC_Custard_Syntax.e with
         | FStarC_Custard_Syntax.EMatch uu___1 -> r
         | uu___1 -> reduce r)
      else
        (let uu___1 =
           let uu___2 =
             let uu___3 = FStarC_List.map reduce_branch brs in
             (scrut1, uu___3) in
           FStarC_Custard_Syntax.EMatch uu___2 in
         {
           FStarC_Custard_Syntax.e = uu___1;
           FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
           FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
         })
  | FStarC_Custard_Syntax.EConst uu___ -> x
  | FStarC_Custard_Syntax.EVar uu___ -> x
  | FStarC_Custard_Syntax.EQual uu___ -> x
  | FStarC_Custard_Syntax.EAny -> x
  | FStarC_Custard_Syntax.EAbort uu___ -> x
  | FStarC_Custard_Syntax.ELet (v, ty, e1, e2) ->
      let e11 = reduce e1 in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Options.custard_backend () in uu___4 = "C" in
            if uu___3
            then
              match e11.FStarC_Custard_Syntax.e with
              | FStarC_Custard_Syntax.EFun _0 -> true
              | uu___4 -> false
            else false in
          if uu___2
          then let uu___3 = count v e2 in uu___3 <= Prims.int_one
          else false in
        if uu___1 then called_only v e2 else false in
      if uu___
      then
        let sm = FStarC_SMap.create (Prims.of_int 5) in
        (FStarC_SMap.add sm v e11; (let uu___2 = sub sm e2 in reduce uu___2))
      else
        (let uu___1 =
           let uu___2 =
             match e11.FStarC_Custard_Syntax.e with
             | FStarC_Custard_Syntax.ECtor (uu___3, es) ->
                 FStarC_List.for_all reeval es
             | FStarC_Custard_Syntax.ETuple es ->
                 FStarC_List.for_all reeval es
             | FStarC_Custard_Syntax.ERecord (uu___3, fs) ->
                 FStarC_List.for_all
                   (fun uu___4 -> match uu___4 with | (uu___5, e) -> reeval e)
                   fs
             | uu___3 -> false in
           if uu___2 then destructed_only v e2 else false in
         if uu___1
         then
           let sm = FStarC_SMap.create (Prims.of_int 5) in
           (FStarC_SMap.add sm v e11;
            (let uu___3 = sub sm e2 in reduce uu___3))
         else
           (let uu___2 =
              let uu___3 = let uu___4 = reduce e2 in (v, ty, e11, uu___4) in
              FStarC_Custard_Syntax.ELet uu___3 in
            {
              FStarC_Custard_Syntax.e = uu___2;
              FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
              FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
            }))
  | uu___ -> FStarC_Custard_Syntax.map_children reduce x
and reduce_branch (br : FStarC_Custard_Syntax.branch) :
  FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 =
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g1 ->
            let uu___2 = reduce g1 in FStar_Pervasives_Native.Some uu___2 in
      let uu___2 = reduce b in (p, uu___1, uu___2)
let reduce_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 = reduce dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
let rec inline_expr
  (tbl :
    (FStarC_Custard_Syntax.binder Prims.list * FStarC_Custard_Syntax.expr)
      FStarC_SMap.t)
  (used : Prims.bool FStarC_SMap.t) (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  let g = inline_expr tbl used in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EApp
      ({ FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual (n, tys);
         FStarC_Custard_Syntax.ty = uu___;
         FStarC_Custard_Syntax.eff = uu___1;_},
       args)
      ->
      let args1 = FStarC_List.map g args in
      let uu___2 =
        let uu___3 = FStarC_Custard_Syntax.string_of_name n in
        FStarC_SMap.try_find tbl uu___3 in
      (match uu___2 with
       | FStar_Pervasives_Native.Some (bs, body) when
           (FStarC_List.length bs) <= (FStarC_List.length args1) ->
           let uu___3 = FStarC_List.splitAt (FStarC_List.length bs) args1 in
           (match uu___3 with
            | (given, extra) ->
                let r = inline_call bs body given x in
                (match extra with
                 | [] -> r
                 | uu___4 ->
                     {
                       FStarC_Custard_Syntax.e =
                         (FStarC_Custard_Syntax.EApp (r, extra));
                       FStarC_Custard_Syntax.ty =
                         (x.FStarC_Custard_Syntax.ty);
                       FStarC_Custard_Syntax.eff =
                         (x.FStarC_Custard_Syntax.eff)
                     }))
       | uu___3 ->
           ((let uu___5 = FStarC_Custard_Syntax.string_of_name n in
             FStarC_SMap.add used uu___5 true);
            {
              FStarC_Custard_Syntax.e =
                (FStarC_Custard_Syntax.EApp
                   ({
                      FStarC_Custard_Syntax.e =
                        (FStarC_Custard_Syntax.EQual (n, tys));
                      FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                      FStarC_Custard_Syntax.eff =
                        (x.FStarC_Custard_Syntax.eff)
                    }, args1));
              FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
              FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
            }))
  | FStarC_Custard_Syntax.EQual (n, uu___) ->
      let uu___1 =
        let uu___2 = FStarC_Custard_Syntax.string_of_name n in
        FStarC_SMap.try_find tbl uu___2 in
      (match uu___1 with
       | FStar_Pervasives_Native.Some ([], body) -> inline_call [] body [] x
       | uu___2 ->
           ((let uu___4 = FStarC_Custard_Syntax.string_of_name n in
             FStarC_SMap.add used uu___4 true);
            x))
  | uu___ -> FStarC_Custard_Syntax.map_children g x
let rec split_last :
  'a . 'a Prims.list -> ('a Prims.list * 'a) FStar_Pervasives_Native.option =
  fun es ->
    match es with
    | [] -> FStar_Pervasives_Native.None
    | e::[] -> FStar_Pervasives_Native.Some ([], e)
    | e::es1 ->
        let uu___ = split_last es1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (pre, last) ->
             FStar_Pervasives_Native.Some ((e :: pre), last)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec eta_reduce (bs : FStarC_Custard_Syntax.binder Prims.list)
  (body : FStarC_Custard_Syntax.expr) (ret : FStarC_Custard_Syntax.cty)
  (ef : FStarC_Custard_Syntax.eff) :
  (FStarC_Custard_Syntax.binder Prims.list * FStarC_Custard_Syntax.expr *
    FStarC_Custard_Syntax.cty * FStarC_Custard_Syntax.eff)=
  let uu___ =
    let uu___1 = split_last bs in (uu___1, (body.FStarC_Custard_Syntax.e)) in
  match uu___ with
  | (FStar_Pervasives_Native.Some (bs', b), FStarC_Custard_Syntax.EApp
     (f, args)) when match bs' with | hd::tl -> true | uu___1 -> false ->
      let uu___1 = split_last args in
      (match uu___1 with
       | FStar_Pervasives_Native.Some
           (args',
            { FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EVar v;
              FStarC_Custard_Syntax.ty = uu___2;
              FStarC_Custard_Syntax.eff = uu___3;_})
           when
           let uu___4 =
             if
               (v = b.FStarC_Custard_Syntax.b_name) &&
                 (FStarC_Custard_Syntax.is_pure f.FStarC_Custard_Syntax.eff)
             then let uu___5 = occurs v f in Prims.not uu___5
             else false in
           if uu___4
           then
             let uu___5 = FStarC_List.existsb (occurs v) args' in
             Prims.not uu___5
           else false ->
           let ret' =
             FStarC_Custard_Syntax.TArrow
               ((b.FStarC_Custard_Syntax.b_ty), ef, ret) in
           let body' =
             match args' with
             | [] ->
                 {
                   FStarC_Custard_Syntax.e = (f.FStarC_Custard_Syntax.e);
                   FStarC_Custard_Syntax.ty = ret';
                   FStarC_Custard_Syntax.eff = (f.FStarC_Custard_Syntax.eff)
                 }
             | uu___4 ->
                 {
                   FStarC_Custard_Syntax.e =
                     (FStarC_Custard_Syntax.EApp (f, args'));
                   FStarC_Custard_Syntax.ty = ret';
                   FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
                 } in
           eta_reduce bs' body' ret' FStarC_Custard_Syntax.E_Pure
       | uu___2 -> (bs, body, ret, ef))
  | uu___1 -> (bs, body, ret, ef)
let rec cheap_expr (x : FStarC_Custard_Syntax.expr) : Prims.bool=
  if FStarC_Custard_Syntax.is_pure x.FStarC_Custard_Syntax.eff
  then
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EConst uu___ -> true
    | FStarC_Custard_Syntax.EVar uu___ -> true
    | FStarC_Custard_Syntax.EQual uu___ -> true
    | FStarC_Custard_Syntax.EApp (f, args) ->
        let uu___ = cheap_expr f in
        (if uu___ then FStarC_List.for_all cheap_expr args else false)
    | FStarC_Custard_Syntax.ECast (e, uu___) -> cheap_expr e
    | FStarC_Custard_Syntax.ECoerce (e, uu___) -> cheap_expr e
    | FStarC_Custard_Syntax.EProj (e, uu___, uu___1) -> cheap_expr e
    | FStarC_Custard_Syntax.EFun uu___ -> true
    | FStarC_Custard_Syntax.EOp (uu___, es) ->
        FStarC_List.for_all cheap_expr es
    | FStarC_Custard_Syntax.ECtor (uu___, es) ->
        FStarC_List.for_all cheap_expr es
    | FStarC_Custard_Syntax.ETuple es -> FStarC_List.for_all cheap_expr es
    | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
        FStarC_List.for_all
          (fun uu___1 -> match uu___1 with | (uu___2, e) -> cheap_expr e) fs
    | FStarC_Custard_Syntax.EDiscrim (e, uu___) -> cheap_expr e
    | uu___ -> false
  else false
let rec arrow_arity (c : FStarC_Custard_Syntax.cty) : Prims.int=
  match c with
  | FStarC_Custard_Syntax.TArrow (uu___, uu___1, b) ->
      let uu___2 = arrow_arity b in Prims.int_one + uu___2
  | uu___ -> Prims.int_zero
let decl_arity (prog : FStarC_Custard_Syntax.program) :
  Prims.int FStarC_SMap.t=
  let tbl = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               l.FStarC_Custard_Syntax.dl_name in
           let uu___2 =
             if
               match l.FStarC_Custard_Syntax.dl_binders with
               | hd::tl -> true
               | uu___3 -> false
             then FStarC_List.length l.FStarC_Custard_Syntax.dl_binders
             else arrow_arity l.FStarC_Custard_Syntax.dl_ret in
           FStarC_SMap.add tbl uu___1 uu___2
       | FStarC_Custard_Syntax.DExternal x ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               x.FStarC_Custard_Syntax.dx_name in
           let uu___2 = arrow_arity x.FStarC_Custard_Syntax.dx_ty in
           FStarC_SMap.add tbl uu___1 uu___2
       | uu___1 -> ()) prog;
  tbl
let decl_binder_names (prog : FStarC_Custard_Syntax.program) :
  Prims.string Prims.list FStarC_SMap.t=
  let tbl = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               l.FStarC_Custard_Syntax.dl_name in
           let uu___2 =
             FStarC_List.map
               (fun b ->
                  FStarC_Custard_Syntax.base_name
                    b.FStarC_Custard_Syntax.b_name)
               l.FStarC_Custard_Syntax.dl_binders in
           FStarC_SMap.add tbl uu___1 uu___2
       | uu___1 -> ()) prog;
  tbl
let rec expr_uses (acc : Prims.int FStarC_SMap.t)
  (x : FStarC_Custard_Syntax.expr) : unit=
  let note n k =
    let s = FStarC_Custard_Syntax.string_of_name n in
    let uu___ = FStarC_SMap.try_find acc s in
    match uu___ with
    | FStar_Pervasives_Native.Some m when m <= k -> ()
    | uu___1 -> FStarC_SMap.add acc s k in
  let sub1 es = FStarC_List.iter (expr_uses acc) es in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EApp
      ({ FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual (n, uu___);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       es)
      -> (note n (FStarC_List.length es); sub1 es)
  | FStarC_Custard_Syntax.EQual (n, uu___) -> note n Prims.int_zero
  | uu___ -> FStarC_Custard_Syntax.iter_children (expr_uses acc) x
let use_arity (prog : FStarC_Custard_Syntax.program) :
  Prims.int FStarC_SMap.t=
  let tbl = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l ->
           let growable =
             let uu___1 =
               if
                 FStarC_Custard_Syntax.is_pure l.FStarC_Custard_Syntax.dl_eff
               then cheap_expr l.FStarC_Custard_Syntax.dl_body
               else false in
             if uu___1
             then
               let uu___2 = arrow_arity l.FStarC_Custard_Syntax.dl_ret in
               uu___2 > Prims.int_zero
             else false in
           (match (l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e
            with
            | FStarC_Custard_Syntax.EQual uu___1 when growable -> ()
            | FStarC_Custard_Syntax.EApp
                ({
                   FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual
                     uu___1;
                   FStarC_Custard_Syntax.ty = uu___2;
                   FStarC_Custard_Syntax.eff = uu___3;_},
                 es)
                when growable -> FStarC_List.iter (expr_uses tbl) es
            | uu___1 -> expr_uses tbl l.FStarC_Custard_Syntax.dl_body)
       | uu___1 -> ()) prog;
  tbl
let eta_expand_decl (tbl : Prims.int FStarC_SMap.t)
  (uses : Prims.int FStarC_SMap.t) (l : FStarC_Custard_Syntax.dlet) :
  FStarC_Custard_Syntax.dlet=
  let rec absorb n bs body ret ef =
    match body.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EFun (lbs, lbody) when
        (match lbs with | hd::tl -> true | uu___ -> false) &&
          ((FStarC_List.length lbs) <= n)
        ->
        let rec peel n1 t e =
          if n1 <= Prims.int_zero
          then FStar_Pervasives_Native.Some (t, e)
          else
            (match t with
             | FStarC_Custard_Syntax.TArrow (uu___, e', b) ->
                 peel (n1 - Prims.int_one) b e'
             | uu___ -> FStar_Pervasives_Native.None) in
        let uu___ = peel (FStarC_List.length lbs) ret ef in
        (match uu___ with
         | FStar_Pervasives_Native.Some (ret', ef') ->
             absorb (n - (FStarC_List.length lbs)) (FStarC_List.op_At bs lbs)
               lbody ret' ef'
         | FStar_Pervasives_Native.None -> (bs, body, ret, ef))
    | uu___ -> (bs, body, ret, ef) in
  let absorb_room =
    let uu___ =
      let uu___1 =
        FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
      FStarC_SMap.try_find uses uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some k ->
        let r = k - (FStarC_List.length l.FStarC_Custard_Syntax.dl_binders) in
        if r < Prims.int_zero then Prims.int_zero else r
    | FStar_Pervasives_Native.None ->
        arrow_arity l.FStarC_Custard_Syntax.dl_ret in
  let uu___ =
    absorb absorb_room l.FStarC_Custard_Syntax.dl_binders
      l.FStarC_Custard_Syntax.dl_body l.FStarC_Custard_Syntax.dl_ret
      l.FStarC_Custard_Syntax.dl_eff in
  match uu___ with
  | (abs_bs, abs_body, abs_ret, abs_ef) ->
      let l1 =
        {
          FStarC_Custard_Syntax.dl_name = (l.FStarC_Custard_Syntax.dl_name);
          FStarC_Custard_Syntax.dl_typars =
            (l.FStarC_Custard_Syntax.dl_typars);
          FStarC_Custard_Syntax.dl_binders = abs_bs;
          FStarC_Custard_Syntax.dl_ret = abs_ret;
          FStarC_Custard_Syntax.dl_eff = abs_ef;
          FStarC_Custard_Syntax.dl_body = abs_body;
          FStarC_Custard_Syntax.dl_flags = (l.FStarC_Custard_Syntax.dl_flags)
        } in
      let missing =
        let uu___1 =
          if
            Prims.not
              (FStarC_Custard_Syntax.is_pure l1.FStarC_Custard_Syntax.dl_eff)
          then true
          else
            (let uu___2 = cheap_expr l1.FStarC_Custard_Syntax.dl_body in
             Prims.not uu___2) in
        if uu___1
        then Prims.int_zero
        else
          (let uu___2 =
             match (l1.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e
             with
             | FStarC_Custard_Syntax.EApp
                 ({
                    FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual
                      (n, uu___3);
                    FStarC_Custard_Syntax.ty = uu___4;
                    FStarC_Custard_Syntax.eff = uu___5;_},
                  args)
                 ->
                 ((FStar_Pervasives_Native.Some n),
                   (FStarC_List.length args))
             | FStarC_Custard_Syntax.EQual (n, uu___3) ->
                 ((FStar_Pervasives_Native.Some n), Prims.int_zero)
             | uu___3 -> (FStar_Pervasives_Native.None, Prims.int_zero) in
           match uu___2 with
           | (head, nargs) ->
               (match head with
                | FStar_Pervasives_Native.None ->
                    let uu___3 =
                      let uu___4 =
                        FStarC_Custard_Syntax.string_of_name
                          l1.FStarC_Custard_Syntax.dl_name in
                      FStarC_SMap.try_find uses uu___4 in
                    (match uu___3 with
                     | FStar_Pervasives_Native.Some k ->
                         let room =
                           k -
                             (FStarC_List.length
                                l1.FStarC_Custard_Syntax.dl_binders) in
                         let have =
                           arrow_arity l1.FStarC_Custard_Syntax.dl_ret in
                         if room <= Prims.int_zero
                         then Prims.int_zero
                         else if room < have then room else have
                     | FStar_Pervasives_Native.None -> Prims.int_zero)
                | FStar_Pervasives_Native.Some n ->
                    let uu___3 =
                      let uu___4 = FStarC_Custard_Syntax.string_of_name n in
                      FStarC_SMap.try_find tbl uu___4 in
                    (match uu___3 with
                     | FStar_Pervasives_Native.Some a when a > nargs ->
                         let want = a - nargs in
                         let have =
                           arrow_arity l1.FStarC_Custard_Syntax.dl_ret in
                         let room =
                           let uu___4 =
                             let uu___5 =
                               FStarC_Custard_Syntax.string_of_name
                                 l1.FStarC_Custard_Syntax.dl_name in
                             FStarC_SMap.try_find uses uu___5 in
                           match uu___4 with
                           | FStar_Pervasives_Native.Some k ->
                               if
                                 (k -
                                    (FStarC_List.length
                                       l1.FStarC_Custard_Syntax.dl_binders))
                                   < Prims.int_zero
                               then Prims.int_zero
                               else
                                 k -
                                   (FStarC_List.length
                                      l1.FStarC_Custard_Syntax.dl_binders)
                           | FStar_Pervasives_Native.None -> have in
                         let m = if want < have then want else have in
                         if room < m then room else m
                     | uu___4 -> Prims.int_zero))) in
      let rec go n bs body ret ef =
        if n <= Prims.int_zero
        then (bs, body, ret, ef)
        else
          (match ret with
           | FStarC_Custard_Syntax.TArrow (a, e, b) ->
               let v = rename "eta" in
               let arg =
                 FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EVar v) a
                   FStarC_Custard_Syntax.E_Pure in
               let body' =
                 match body.FStarC_Custard_Syntax.e with
                 | FStarC_Custard_Syntax.EApp (f, args) ->
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EApp
                          (f, (FStarC_List.op_At args [arg]))) b e
                 | uu___1 ->
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EApp (body, [arg])) b e in
               go (n - Prims.int_one)
                 (FStarC_List.op_At bs
                    [{
                       FStarC_Custard_Syntax.b_name = v;
                       FStarC_Custard_Syntax.b_ty = a
                     }]) body' b e
           | uu___1 -> (bs, body, ret, ef)) in
      let uu___1 =
        go missing l1.FStarC_Custard_Syntax.dl_binders
          l1.FStarC_Custard_Syntax.dl_body l1.FStarC_Custard_Syntax.dl_ret
          l1.FStarC_Custard_Syntax.dl_eff in
      (match uu___1 with
       | (bs, body, ret, ef) ->
           {
             FStarC_Custard_Syntax.dl_name =
               (l1.FStarC_Custard_Syntax.dl_name);
             FStarC_Custard_Syntax.dl_typars =
               (l1.FStarC_Custard_Syntax.dl_typars);
             FStarC_Custard_Syntax.dl_binders = bs;
             FStarC_Custard_Syntax.dl_ret = ret;
             FStarC_Custard_Syntax.dl_eff = ef;
             FStarC_Custard_Syntax.dl_body = body;
             FStarC_Custard_Syntax.dl_flags =
               (l1.FStarC_Custard_Syntax.dl_flags)
           })
let eta_expand_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let width p =
    FStarC_List.fold_left
      (fun n d ->
         match d with
         | FStarC_Custard_Syntax.DLet l ->
             n + (FStarC_List.length l.FStarC_Custard_Syntax.dl_binders)
         | uu___ -> n) Prims.int_zero p in
  let rec go fuel p =
    let tbl = decl_arity p in
    let uses = use_arity p in
    let p' =
      FStarC_List.map
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DLet l ->
               let uu___ = eta_expand_decl tbl uses l in
               FStarC_Custard_Syntax.DLet uu___
           | d1 -> d1) p in
    let uu___ =
      if fuel <= Prims.int_zero
      then true
      else (let uu___1 = width p' in let uu___2 = width p in uu___1 = uu___2) in
    if uu___ then p' else go (fuel - Prims.int_one) p' in
  go (FStarC_List.length prog) prog
let eta_rename_decl (bnames : Prims.string Prims.list FStarC_SMap.t)
  (l : FStarC_Custard_Syntax.dlet) : FStarC_Custard_Syntax.dlet=
  match (l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EApp
      ({ FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual (n, uu___);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       args)
      ->
      let uu___3 =
        let uu___4 = FStarC_Custard_Syntax.string_of_name n in
        FStarC_SMap.try_find bnames uu___4 in
      (match uu___3 with
       | FStar_Pervasives_Native.None -> l
       | FStar_Pervasives_Native.Some ns ->
           let sm = FStarC_SMap.create (Prims.of_int 10) in
           let pairs = FStarC_Effect.mk_ref [] in
           let bound v =
             FStarC_List.existsb
               (fun b -> b.FStarC_Custard_Syntax.b_name = v)
               l.FStarC_Custard_Syntax.dl_binders in
           (FStarC_List.iteri
              (fun j a ->
                 match a.FStarC_Custard_Syntax.e with
                 | FStarC_Custard_Syntax.EVar v when
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStarC_Custard_Syntax.base_name v in
                         uu___7 = "eta" in
                       if uu___6 then bound v else false in
                     if uu___5
                     then
                       let uu___6 = FStarC_SMap.try_find sm v in
                       match uu___6 with
                       | FStar_Pervasives_Native.None -> true
                       | uu___7 -> false
                     else false ->
                     if j < (FStarC_List.length ns)
                     then
                       let nm = FStarC_List.nth ns j in
                       let uu___5 =
                         if nm <> ""
                         then
                           let uu___6 = FStarC_Custard_Syntax.base_name nm in
                           uu___6 <> "eta"
                         else false in
                       (if uu___5
                        then
                          let nv = rename nm in
                          (FStarC_SMap.add sm v
                             (FStarC_Custard_Syntax.mk
                                (FStarC_Custard_Syntax.EVar nv)
                                a.FStarC_Custard_Syntax.ty
                                a.FStarC_Custard_Syntax.eff);
                           (let uu___7 =
                              let uu___8 = FStarC_Effect.op_Bang pairs in
                              (v, nv) :: uu___8 in
                            FStarC_Effect.op_Colon_Equals pairs uu___7))
                        else ())
                     else ()
                 | uu___5 -> ()) args;
            (let uu___5 =
               let uu___6 = FStarC_Effect.op_Bang pairs in
               match uu___6 with | [] -> true | uu___7 -> false in
             if uu___5
             then l
             else
               (let rn v =
                  let uu___6 =
                    let uu___7 = FStarC_Effect.op_Bang pairs in
                    FStarC_List.tryFind
                      (fun uu___8 -> match uu___8 with | (a, uu___9) -> a = v)
                      uu___7 in
                  match uu___6 with
                  | FStar_Pervasives_Native.Some (uu___7, nv) -> nv
                  | FStar_Pervasives_Native.None -> v in
                let uu___6 =
                  FStarC_List.map
                    (fun b ->
                       let uu___7 = rn b.FStarC_Custard_Syntax.b_name in
                       {
                         FStarC_Custard_Syntax.b_name = uu___7;
                         FStarC_Custard_Syntax.b_ty =
                           (b.FStarC_Custard_Syntax.b_ty)
                       }) l.FStarC_Custard_Syntax.dl_binders in
                let uu___7 = sub sm l.FStarC_Custard_Syntax.dl_body in
                {
                  FStarC_Custard_Syntax.dl_name =
                    (l.FStarC_Custard_Syntax.dl_name);
                  FStarC_Custard_Syntax.dl_typars =
                    (l.FStarC_Custard_Syntax.dl_typars);
                  FStarC_Custard_Syntax.dl_binders = uu___6;
                  FStarC_Custard_Syntax.dl_ret =
                    (l.FStarC_Custard_Syntax.dl_ret);
                  FStarC_Custard_Syntax.dl_eff =
                    (l.FStarC_Custard_Syntax.dl_eff);
                  FStarC_Custard_Syntax.dl_body = uu___7;
                  FStarC_Custard_Syntax.dl_flags =
                    (l.FStarC_Custard_Syntax.dl_flags)
                }))))
  | uu___ -> l
let eta_rename_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let anon p =
    FStarC_List.fold_left
      (fun n d ->
         match d with
         | FStarC_Custard_Syntax.DLet l ->
             FStarC_List.fold_left
               (fun n1 b ->
                  let uu___ =
                    let uu___1 =
                      FStarC_Custard_Syntax.base_name
                        b.FStarC_Custard_Syntax.b_name in
                    uu___1 = "eta" in
                  if uu___ then n1 + Prims.int_one else n1) n
               l.FStarC_Custard_Syntax.dl_binders
         | uu___ -> n) Prims.int_zero p in
  let rec go fuel p =
    let bnames = decl_binder_names p in
    let p' =
      FStarC_List.map
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DLet l ->
               let uu___ = eta_rename_decl bnames l in
               FStarC_Custard_Syntax.DLet uu___
           | d1 -> d1) p in
    let uu___ =
      if fuel <= Prims.int_zero
      then true
      else (let uu___1 = anon p' in let uu___2 = anon p in uu___1 = uu___2) in
    if uu___ then p' else go (fuel - Prims.int_one) p' in
  go (FStarC_List.length prog) prog
let eta_reduce_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l ->
           let uu___ =
             eta_reduce l.FStarC_Custard_Syntax.dl_binders
               l.FStarC_Custard_Syntax.dl_body l.FStarC_Custard_Syntax.dl_ret
               l.FStarC_Custard_Syntax.dl_eff in
           (match uu___ with
            | (bs, body, ret, ef) ->
                FStarC_Custard_Syntax.DLet
                  {
                    FStarC_Custard_Syntax.dl_name =
                      (l.FStarC_Custard_Syntax.dl_name);
                    FStarC_Custard_Syntax.dl_typars =
                      (l.FStarC_Custard_Syntax.dl_typars);
                    FStarC_Custard_Syntax.dl_binders = bs;
                    FStarC_Custard_Syntax.dl_ret = ret;
                    FStarC_Custard_Syntax.dl_eff = ef;
                    FStarC_Custard_Syntax.dl_body = body;
                    FStarC_Custard_Syntax.dl_flags =
                      (l.FStarC_Custard_Syntax.dl_flags)
                  })
       | d1 -> d1) prog
let rec cty_deps (c : FStarC_Custard_Syntax.cty) : Prims.string Prims.list=
  match c with
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ = FStarC_Custard_Syntax.string_of_name n in
      let uu___1 = FStarC_List.collect cty_deps args in uu___ :: uu___1
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = cty_deps a in
      let uu___2 = cty_deps b in FStarC_List.op_At uu___1 uu___2
  | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.collect cty_deps cs
  | FStarC_Custard_Syntax.TBuf c1 -> cty_deps c1
  | FStarC_Custard_Syntax.TRef c1 -> cty_deps c1
  | FStarC_Custard_Syntax.TInline c1 -> cty_deps c1
  | uu___ -> []
let rec pat_deps (p : FStarC_Custard_Syntax.pat) : Prims.string Prims.list=
  match p with
  | FStarC_Custard_Syntax.PCtor (n, ps) ->
      let uu___ = FStarC_Custard_Syntax.string_of_name n in
      let uu___1 = FStarC_List.collect pat_deps ps in uu___ :: uu___1
  | FStarC_Custard_Syntax.PRecord (n, fs) ->
      let uu___ = FStarC_Custard_Syntax.string_of_name n in
      let uu___1 =
        FStarC_List.collect
          (fun uu___2 -> match uu___2 with | (uu___3, q) -> pat_deps q) fs in
      uu___ :: uu___1
  | FStarC_Custard_Syntax.PTuple ps -> FStarC_List.collect pat_deps ps
  | FStarC_Custard_Syntax.POr ps -> FStarC_List.collect pat_deps ps
  | uu___ -> []
let rec expr_deps (x : FStarC_Custard_Syntax.expr) : Prims.string Prims.list=
  let ds = cty_deps x.FStarC_Custard_Syntax.ty in
  let sub1 es = FStarC_List.collect expr_deps es in
  let uu___ =
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EQual (n, tys) ->
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        let uu___2 = FStarC_List.collect cty_deps tys in uu___1 :: uu___2
    | FStarC_Custard_Syntax.ECtor (n, es) ->
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        let uu___2 = sub1 es in uu___1 :: uu___2
    | FStarC_Custard_Syntax.ERaise e1 -> expr_deps e1
    | FStarC_Custard_Syntax.ERecord (n, fs) ->
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        let uu___2 =
          let uu___3 = FStarC_List.map FStar_Pervasives_Native.snd fs in
          sub1 uu___3 in
        uu___1 :: uu___2
    | FStarC_Custard_Syntax.EDiscrim (e, n) ->
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        let uu___2 = expr_deps e in uu___1 :: uu___2
    | FStarC_Custard_Syntax.EProj (e, n, uu___1) ->
        let uu___2 = FStarC_Custard_Syntax.string_of_name n in
        let uu___3 = expr_deps e in uu___2 :: uu___3
    | FStarC_Custard_Syntax.ELet (uu___1, t, e1, e2) ->
        let uu___2 = cty_deps t in
        let uu___3 = sub1 [e1; e2] in FStarC_List.op_At uu___2 uu___3
    | FStarC_Custard_Syntax.EFun (bs, b) ->
        let uu___1 =
          FStarC_List.collect
            (fun b1 -> cty_deps b1.FStarC_Custard_Syntax.b_ty) bs in
        let uu___2 = expr_deps b in FStarC_List.op_At uu___1 uu___2
    | FStarC_Custard_Syntax.ECast (e, t) ->
        let uu___1 = cty_deps t in
        let uu___2 = expr_deps e in FStarC_List.op_At uu___1 uu___2
    | FStarC_Custard_Syntax.ECoerce (e, t) ->
        let uu___1 = cty_deps t in
        let uu___2 = expr_deps e in FStarC_List.op_At uu___1 uu___2
    | FStarC_Custard_Syntax.EMatch (sc, brs) ->
        let uu___1 = expr_deps sc in
        let uu___2 =
          FStarC_List.collect
            (fun uu___3 ->
               match uu___3 with
               | (p, g, b) ->
                   let uu___4 = pat_deps p in
                   let uu___5 =
                     let uu___6 =
                       match g with
                       | FStar_Pervasives_Native.Some g1 -> expr_deps g1
                       | FStar_Pervasives_Native.None -> [] in
                     let uu___7 = expr_deps b in
                     FStarC_List.op_At uu___6 uu___7 in
                   FStarC_List.op_At uu___4 uu___5) brs in
        FStarC_List.op_At uu___1 uu___2
    | FStarC_Custard_Syntax.ETry (sc, brs) ->
        let uu___1 = expr_deps sc in
        let uu___2 =
          FStarC_List.collect
            (fun uu___3 ->
               match uu___3 with
               | (p, g, b) ->
                   let uu___4 = pat_deps p in
                   let uu___5 =
                     let uu___6 =
                       match g with
                       | FStar_Pervasives_Native.Some g1 -> expr_deps g1
                       | FStar_Pervasives_Native.None -> [] in
                     let uu___7 = expr_deps b in
                     FStarC_List.op_At uu___6 uu___7 in
                   FStarC_List.op_At uu___4 uu___5) brs in
        FStarC_List.op_At uu___1 uu___2
    | uu___1 -> let uu___2 = FStarC_Custard_Syntax.children x in sub1 uu___2 in
  FStarC_List.op_At ds uu___
let decl_deps (d : FStarC_Custard_Syntax.decl) : Prims.string Prims.list=
  match d with
  | FStarC_Custard_Syntax.DLet l ->
      let uu___ =
        FStarC_List.collect (fun b -> cty_deps b.FStarC_Custard_Syntax.b_ty)
          l.FStarC_Custard_Syntax.dl_binders in
      let uu___1 =
        let uu___2 = cty_deps l.FStarC_Custard_Syntax.dl_ret in
        let uu___3 = expr_deps l.FStarC_Custard_Syntax.dl_body in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.DType t ->
      (match t.FStarC_Custard_Syntax.dt_body with
       | FStarC_Custard_Syntax.TAbbrev c -> cty_deps c
       | FStarC_Custard_Syntax.TRecord fs ->
           FStarC_List.collect
             (fun uu___ -> match uu___ with | (uu___1, c) -> cty_deps c) fs
       | FStarC_Custard_Syntax.TVariant cs ->
           FStarC_List.collect
             (fun uu___ ->
                match uu___ with
                | (uu___1, fs) ->
                    FStarC_List.collect
                      (fun uu___2 ->
                         match uu___2 with | (uu___3, c) -> cty_deps c) fs)
             cs
       | FStarC_Custard_Syntax.TAbstract -> [])
  | FStarC_Custard_Syntax.DExternal x ->
      cty_deps x.FStarC_Custard_Syntax.dx_ty
  | FStarC_Custard_Syntax.DExn e ->
      FStarC_List.collect cty_deps e.FStarC_Custard_Syntax.de_args
let is_identity (dl : FStarC_Custard_Syntax.dlet) : Prims.bool=
  let uu___ =
    let uu___1 = arrow_arity dl.FStarC_Custard_Syntax.dl_ret in
    uu___1 = Prims.int_zero in
  if uu___
  then
    match ((dl.FStarC_Custard_Syntax.dl_binders),
            ((dl.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e))
    with
    | (b::[], FStarC_Custard_Syntax.EVar v) ->
        b.FStarC_Custard_Syntax.b_name = v
    | uu___1 -> false
  else false
let inline_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let tbl = FStarC_SMap.create (Prims.of_int 50) in
  let used = FStarC_SMap.create (Prims.of_int 50) in
  let inl = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl when
           let uu___1 =
             FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Inline
               dl.FStarC_Custard_Syntax.dl_flags in
           if uu___1 then true else is_identity dl ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               dl.FStarC_Custard_Syntax.dl_name in
           FStarC_SMap.add inl uu___1 dl
       | uu___1 -> ()) prog;
  (let visiting = FStarC_SMap.create (Prims.of_int 50) in
   let bodies = FStarC_SMap.create (Prims.of_int 50) in
   let rec fill n =
     let uu___1 =
       let uu___2 = FStarC_SMap.try_find visiting n in
       match uu___2 with
       | FStar_Pervasives_Native.None -> true
       | uu___3 -> false in
     if uu___1
     then
       (FStarC_SMap.add visiting n true;
        (let uu___3 = FStarC_SMap.try_find inl n in
         match uu___3 with
         | FStar_Pervasives_Native.Some dl ->
             ((let uu___5 = decl_deps (FStarC_Custard_Syntax.DLet dl) in
               FStarC_List.iter fill uu___5);
              (let body =
                 inline_expr tbl used dl.FStarC_Custard_Syntax.dl_body in
               FStarC_SMap.add bodies n body;
               FStarC_SMap.add tbl n
                 ((dl.FStarC_Custard_Syntax.dl_binders), body)))
         | FStar_Pervasives_Native.None -> ()))
     else () in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl when
            let uu___2 =
              FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Inline
                dl.FStarC_Custard_Syntax.dl_flags in
            if uu___2 then true else is_identity dl ->
            let uu___2 =
              FStarC_Custard_Syntax.string_of_name
                dl.FStarC_Custard_Syntax.dl_name in
            fill uu___2
        | uu___2 -> ()) prog;
   (let prog1 =
      FStarC_List.map
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DLet dl ->
               let uu___2 =
                 let uu___3 =
                   FStarC_Custard_Syntax.string_of_name
                     dl.FStarC_Custard_Syntax.dl_name in
                 FStarC_SMap.try_find bodies uu___3 in
               (match uu___2 with
                | FStar_Pervasives_Native.Some body ->
                    FStarC_Custard_Syntax.DLet
                      {
                        FStarC_Custard_Syntax.dl_name =
                          (dl.FStarC_Custard_Syntax.dl_name);
                        FStarC_Custard_Syntax.dl_typars =
                          (dl.FStarC_Custard_Syntax.dl_typars);
                        FStarC_Custard_Syntax.dl_binders =
                          (dl.FStarC_Custard_Syntax.dl_binders);
                        FStarC_Custard_Syntax.dl_ret =
                          (dl.FStarC_Custard_Syntax.dl_ret);
                        FStarC_Custard_Syntax.dl_eff =
                          (dl.FStarC_Custard_Syntax.dl_eff);
                        FStarC_Custard_Syntax.dl_body = body;
                        FStarC_Custard_Syntax.dl_flags =
                          (dl.FStarC_Custard_Syntax.dl_flags)
                      }
                | FStar_Pervasives_Native.None ->
                    let uu___3 =
                      let uu___4 =
                        inline_expr tbl used dl.FStarC_Custard_Syntax.dl_body in
                      {
                        FStarC_Custard_Syntax.dl_name =
                          (dl.FStarC_Custard_Syntax.dl_name);
                        FStarC_Custard_Syntax.dl_typars =
                          (dl.FStarC_Custard_Syntax.dl_typars);
                        FStarC_Custard_Syntax.dl_binders =
                          (dl.FStarC_Custard_Syntax.dl_binders);
                        FStarC_Custard_Syntax.dl_ret =
                          (dl.FStarC_Custard_Syntax.dl_ret);
                        FStarC_Custard_Syntax.dl_eff =
                          (dl.FStarC_Custard_Syntax.dl_eff);
                        FStarC_Custard_Syntax.dl_body = uu___4;
                        FStarC_Custard_Syntax.dl_flags =
                          (dl.FStarC_Custard_Syntax.dl_flags)
                      } in
                    FStarC_Custard_Syntax.DLet uu___3)
           | d1 -> d1) prog in
    FStarC_List.filter
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DLet dl ->
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Inline
                     dl.FStarC_Custard_Syntax.dl_flags in
                 Prims.not uu___4 in
               if uu___3
               then true
               else
                 FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Root
                   dl.FStarC_Custard_Syntax.dl_flags in
             if uu___2
             then true
             else
               (let uu___3 =
                  let uu___4 =
                    FStarC_Custard_Syntax.string_of_name
                      dl.FStarC_Custard_Syntax.dl_name in
                  FStarC_SMap.try_find used uu___4 in
                match uu___3 with
                | FStar_Pervasives_Native.Some v -> true
                | uu___4 -> false)
         | uu___2 -> true) prog1))
let ctor_owners (prog : FStarC_Custard_Syntax.program) :
  Prims.string FStarC_SMap.t=
  let m = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t ->
           let owner =
             FStarC_Custard_Syntax.string_of_name
               t.FStarC_Custard_Syntax.dt_name in
           (match t.FStarC_Custard_Syntax.dt_body with
            | FStarC_Custard_Syntax.TVariant cs ->
                FStarC_List.iter
                  (fun uu___1 ->
                     match uu___1 with
                     | (cn, uu___2) ->
                         let uu___3 = FStarC_Custard_Syntax.string_of_name cn in
                         FStarC_SMap.add m uu___3 owner) cs
            | uu___1 -> ())
       | uu___1 -> ()) prog;
  m
let entry_module (n : FStarC_Custard_Syntax.name) : Prims.bool=
  let m = FStarC_String.concat "." n.FStarC_Custard_Syntax.ns in
  let uu___ = FStarC_Options.custard_entry_modules () in
  FStarC_List.existsb (fun e -> e = m) uu___
let rec spellable (c : FStarC_Custard_Syntax.cty) : Prims.bool=
  match c with
  | FStarC_Custard_Syntax.TAny -> false
  | FStarC_Custard_Syntax.TExn -> false
  | FStarC_Custard_Syntax.TApp (uu___, args) ->
      FStarC_List.for_all spellable args
  | FStarC_Custard_Syntax.TTuple args -> FStarC_List.for_all spellable args
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = spellable a in if uu___1 then spellable b else false
  | FStarC_Custard_Syntax.TBuf c1 -> spellable c1
  | FStarC_Custard_Syntax.TRef c1 -> spellable c1
  | FStarC_Custard_Syntax.TInline c1 -> spellable c1
  | uu___ -> true
let revive_abbrevs (prog : FStarC_Custard_Syntax.program)
  (live : Prims.bool FStarC_SMap.t) : unit=
  let cands =
    FStarC_List.collect
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DType dt ->
             (match dt.FStarC_Custard_Syntax.dt_body with
              | FStarC_Custard_Syntax.TAbbrev c when
                  let uu___ =
                    let uu___1 =
                      let uu___2 =
                        entry_module dt.FStarC_Custard_Syntax.dt_name in
                      if uu___2
                      then
                        let uu___3 =
                          FStarC_Custard_Syntax.has_flag
                            dt.FStarC_Custard_Syntax.dt_flags
                            FStarC_Custard_Syntax.Private in
                        Prims.not uu___3
                      else false in
                    if uu___1 then spellable c else false in
                  if uu___
                  then
                    let uu___1 =
                      let uu___2 =
                        FStarC_Custard_Syntax.string_of_name
                          dt.FStarC_Custard_Syntax.dt_name in
                      FStarC_SMap.try_find live uu___2 in
                    match uu___1 with
                    | FStar_Pervasives_Native.None -> true
                    | uu___2 -> false
                  else false ->
                  let uu___ =
                    let uu___1 =
                      FStarC_Custard_Syntax.string_of_name
                        dt.FStarC_Custard_Syntax.dt_name in
                    let uu___2 = cty_deps c in (uu___1, uu___2) in
                  [uu___]
              | uu___ -> [])
         | uu___ -> []) prog in
  let rec go fuel =
    if fuel <= Prims.int_zero
    then ()
    else
      (let added =
         FStarC_List.existsb
           (fun uu___ ->
              match uu___ with
              | (n, deps) ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStarC_SMap.try_find live n in
                      match uu___3 with
                      | FStar_Pervasives_Native.None -> true
                      | uu___4 -> false in
                    if uu___2
                    then
                      FStarC_List.for_all
                        (fun d ->
                           let uu___3 = FStarC_SMap.try_find live d in
                           match uu___3 with
                           | FStar_Pervasives_Native.Some v -> true
                           | uu___4 -> false) deps
                    else false in
                  if uu___1
                  then (FStarC_SMap.add live n true; true)
                  else false) cands in
       if added then go (fuel - Prims.int_one) else ()) in
  go ((FStarC_List.length cands) + Prims.int_one)
let dce (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let own = ctor_owners prog in
  let resolve n =
    let uu___ = FStarC_SMap.try_find own n in
    match uu___ with
    | FStar_Pervasives_Native.Some o -> o
    | FStar_Pervasives_Native.None -> n in
  let defs = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       let uu___1 =
         FStarC_Custard_Syntax.string_of_name
           (FStarC_Custard_Syntax.name_of_decl d) in
       FStarC_SMap.add defs uu___1 d) prog;
  (let live = FStarC_SMap.create (Prims.of_int 50) in
   let rec visit n =
     let n1 = resolve n in
     let uu___1 =
       let uu___2 = FStarC_SMap.try_find live n1 in
       match uu___2 with
       | FStar_Pervasives_Native.None -> true
       | uu___3 -> false in
     if uu___1
     then
       (FStarC_SMap.add live n1 true;
        (let uu___3 = FStarC_SMap.try_find defs n1 in
         match uu___3 with
         | FStar_Pervasives_Native.Some d ->
             let uu___4 = decl_deps d in FStarC_List.iter visit uu___4
         | FStar_Pervasives_Native.None -> ()))
     else () in
   FStarC_List.iter
     (fun d ->
        let uu___2 =
          FStarC_List.existsb
            (fun f ->
               (match f with
                | FStarC_Custard_Syntax.Root -> true
                | uu___3 -> false) ||
                 (match f with
                  | FStarC_Custard_Syntax.Entrypoint -> true
                  | uu___3 -> false)) (FStarC_Custard_Syntax.decl_flags d) in
        if uu___2
        then
          let uu___3 =
            FStarC_Custard_Syntax.string_of_name
              (FStarC_Custard_Syntax.name_of_decl d) in
          visit uu___3
        else ()) prog;
   revive_abbrevs prog live;
   FStarC_List.filter
     (fun d ->
        let uu___3 =
          let uu___4 =
            FStarC_Custard_Syntax.string_of_name
              (FStarC_Custard_Syntax.name_of_decl d) in
          FStarC_SMap.try_find live uu___4 in
        match uu___3 with
        | FStar_Pervasives_Native.Some v -> true
        | uu___4 -> false) prog)
let propagate_prologues (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let own = ctor_owners prog in
  let resolve n =
    let uu___ = FStarC_SMap.try_find own n in
    match uu___ with
    | FStar_Pervasives_Native.Some o -> o
    | FStar_Pervasives_Native.None -> n in
  let defs = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       let uu___1 =
         FStarC_Custard_Syntax.string_of_name
           (FStarC_Custard_Syntax.name_of_decl d) in
       FStarC_SMap.add defs uu___1 d) prog;
  (let is_entry d =
     FStarC_List.existsb
       (fun f ->
          (match f with
           | FStarC_Custard_Syntax.Prologue _0 -> true
           | uu___1 -> false) ||
            (match f with
             | FStarC_Custard_Syntax.ClosurePrologue _0 -> true
             | uu___1 -> false)) (FStarC_Custard_Syntax.decl_flags d) in
   let reach stop_at_entry seeds =
     let seen = FStarC_SMap.create (Prims.of_int 50) in
     let rec visit n =
       let n1 = resolve n in
       let uu___1 =
         let uu___2 = FStarC_SMap.try_find seen n1 in
         match uu___2 with
         | FStar_Pervasives_Native.None -> true
         | uu___3 -> false in
       if uu___1
       then
         (FStarC_SMap.add seen n1 true;
          (let uu___3 = FStarC_SMap.try_find defs n1 in
           match uu___3 with
           | FStar_Pervasives_Native.Some d ->
               let uu___4 = if stop_at_entry then is_entry d else false in
               if uu___4
               then ()
               else
                 (let uu___5 = decl_deps d in FStarC_List.iter visit uu___5)
           | FStar_Pervasives_Native.None -> ()))
       else () in
     FStarC_List.iter visit seeds; seen in
   let seeds =
     FStarC_List.collect
       (fun d ->
          let uu___1 =
            FStarC_List.existsb FStarC_Custard_Syntax.uu___is_ClosurePrologue
              (FStarC_Custard_Syntax.decl_flags d) in
          if uu___1
          then
            let uu___2 =
              FStarC_Custard_Syntax.string_of_name
                (FStarC_Custard_Syntax.name_of_decl d) in
            [uu___2]
          else []) prog in
   if match seeds with | [] -> true | uu___1 -> false
   then prog
   else
     (let device =
        let uu___1 =
          FStarC_List.collect
            (fun n ->
               let uu___2 = FStarC_SMap.try_find defs n in
               match uu___2 with
               | FStar_Pervasives_Native.Some d -> decl_deps d
               | FStar_Pervasives_Native.None -> []) seeds in
        reach false uu___1 in
      let host =
        let uu___1 =
          FStarC_List.collect
            (fun d ->
               let uu___2 =
                 let uu___3 =
                   FStarC_List.existsb
                     (fun f ->
                        (match f with
                         | FStarC_Custard_Syntax.Root -> true
                         | uu___4 -> false) ||
                          (match f with
                           | FStarC_Custard_Syntax.Entrypoint -> true
                           | uu___4 -> false))
                     (FStarC_Custard_Syntax.decl_flags d) in
                 if uu___3
                 then let uu___4 = is_entry d in Prims.not uu___4
                 else false in
               if uu___2
               then
                 let uu___3 =
                   FStarC_Custard_Syntax.string_of_name
                     (FStarC_Custard_Syntax.name_of_decl d) in
                 [uu___3]
               else []) prog in
        reach true uu___1 in
      let strings =
        let uu___1 =
          FStarC_List.collect
            (fun d ->
               FStarC_List.collect
                 (fun f ->
                    match f with
                    | FStarC_Custard_Syntax.ClosurePrologue (a, b) ->
                        [(a, b)]
                    | uu___2 -> []) (FStarC_Custard_Syntax.decl_flags d))
            prog in
        match uu___1 with | (a, b)::uu___2 -> (a, b) | [] -> ("", "") in
      let uu___1 = strings in
      match uu___1 with
      | (excl, shared) ->
          let shared_global l =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_Custard_Syntax.string_of_name
                        l.FStarC_Custard_Syntax.dl_name in
                    Prims.strcat uu___6
                      " is reached from device code and from host code." in
                  Prims.strcat "Custard: the global " uu___5 in
                FStarC_Errors_Msg.text uu___4 in
              [uu___3;
              FStarC_Errors_Msg.text
                "It is a variable and not a function, so the second string of custard_c_closure_prologue cannot be applied to it: a qualifier meaning \"reachable from both\" describes a function, and a target that has an answer for variables (CUDA's __managed__) spells it as a storage class with a runtime cost, which is not a decoration Custard may add on its own.";
              FStarC_Errors_Msg.text
                "Applying it anyway would be worse than refusing: on CUDA the host qualifier on a variable is dropped silently, so the result compiles with a warning and is wrong at runtime.";
              FStarC_Errors_Msg.text
                "Either make it a function of unit, so that the closure can decorate it like any other callee, or keep it out of the device closure."] in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Error_CustardSharedGlobal ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___2) in
          FStarC_List.map
            (fun d ->
               match d with
               | FStarC_Custard_Syntax.DLet l ->
                   let n =
                     FStarC_Custard_Syntax.string_of_name
                       l.FStarC_Custard_Syntax.dl_name in
                   if FStarC_List.mem n seeds
                   then d
                   else
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 = FStarC_SMap.try_find device n in
                          match uu___4 with
                          | FStar_Pervasives_Native.Some v -> true
                          | uu___5 -> false in
                        if uu___3
                        then
                          let uu___4 =
                            FStarC_List.existsb
                              FStarC_Custard_Syntax.uu___is_Prologue
                              l.FStarC_Custard_Syntax.dl_flags in
                          Prims.not uu___4
                        else false in
                      if uu___2
                      then
                        let s =
                          let uu___3 =
                            let uu___4 = FStarC_SMap.try_find host n in
                            match uu___4 with
                            | FStar_Pervasives_Native.Some v -> true
                            | uu___5 -> false in
                          if uu___3
                          then
                            (if
                               (match l.FStarC_Custard_Syntax.dl_binders with
                                | [] -> true
                                | uu___5 -> false)
                             then shared_global l
                             else ();
                             shared)
                          else excl in
                        FStarC_Custard_Syntax.DLet
                          {
                            FStarC_Custard_Syntax.dl_name =
                              (l.FStarC_Custard_Syntax.dl_name);
                            FStarC_Custard_Syntax.dl_typars =
                              (l.FStarC_Custard_Syntax.dl_typars);
                            FStarC_Custard_Syntax.dl_binders =
                              (l.FStarC_Custard_Syntax.dl_binders);
                            FStarC_Custard_Syntax.dl_ret =
                              (l.FStarC_Custard_Syntax.dl_ret);
                            FStarC_Custard_Syntax.dl_eff =
                              (l.FStarC_Custard_Syntax.dl_eff);
                            FStarC_Custard_Syntax.dl_body =
                              (l.FStarC_Custard_Syntax.dl_body);
                            FStarC_Custard_Syntax.dl_flags =
                              ((FStarC_Custard_Syntax.Prologue s) ::
                              (l.FStarC_Custard_Syntax.dl_flags))
                          }
                      else d)
               | d1 -> d1) prog))
let check_resolved (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Options.custard_unit () in
      match uu___2 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___3 -> false in
    if uu___1
    then true
    else
      (let uu___2 = FStarC_Options.custard_links () in
       match uu___2 with | hd::tl -> true | uu___3 -> false) in
  if uu___
  then prog
  else
    (let defs = FStarC_SMap.create (Prims.of_int 50) in
     FStarC_List.iter
       (fun d ->
          let uu___2 =
            FStarC_Custard_Syntax.string_of_name
              (FStarC_Custard_Syntax.name_of_decl d) in
          FStarC_SMap.add defs uu___2 true) prog;
     (let rec quals x =
        let sub1 es = FStarC_List.collect quals es in
        match x.FStarC_Custard_Syntax.e with
        | FStarC_Custard_Syntax.EQual (n, uu___2) -> [n]
        | uu___2 ->
            let uu___3 = FStarC_Custard_Syntax.children x in sub1 uu___3 in
      FStarC_List.iter
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DLet l ->
               let uu___3 = quals l.FStarC_Custard_Syntax.dl_body in
               FStarC_List.iter
                 (fun n ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStarC_Custard_Syntax.string_of_name n in
                        FStarC_SMap.try_find defs uu___6 in
                      match uu___5 with
                      | FStar_Pervasives_Native.None -> true
                      | uu___6 -> false in
                    if uu___4
                    then
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStarC_Custard_Syntax.string_of_name
                                  l.FStarC_Custard_Syntax.dl_name in
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_Custard_Syntax.string_of_name n in
                                  Prims.strcat uu___12
                                    ", which is not in the program." in
                                Prims.strcat " refers to " uu___11 in
                              Prims.strcat uu___9 uu___10 in
                            Prims.strcat "Custard: " uu___8 in
                          FStarC_Errors_Msg.text uu___7 in
                        [uu___6;
                        FStarC_Errors_Msg.text
                          "Nothing declares it, so the generated code would not compile, and if it is an external its target name and header were never read either.";
                        FStarC_Errors_Msg.text
                          "A rule that synthesizes a call to a runtime entry point has to keep it alive: register it with FStarC.Custard.Builtins.register_root, next to the rule itself (section 36.2).  Otherwise this is a misspelled name."] in
                      FStarC_Errors.raise_error0
                        FStarC_Errors_Codes.Error_CustardDanglingReference ()
                        (Obj.magic
                           FStarC_Errors_Msg.is_error_message_list_doc)
                        (Obj.magic uu___5)
                    else ()) uu___3
           | uu___3 -> ()) prog;
      prog))
let scc (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let own = ctor_owners prog in
  let key d =
    FStarC_Custard_Syntax.string_of_name
      (FStarC_Custard_Syntax.name_of_decl d) in
  let defs = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d -> let uu___1 = key d in FStarC_SMap.add defs uu___1 d) prog;
  (let pos = FStarC_SMap.create (Prims.of_int 50) in
   let uu___1 =
     FStarC_List.fold_left
       (fun i d ->
          (let uu___3 = key d in FStarC_SMap.add pos uu___3 i);
          i + Prims.int_one) Prims.int_zero prog in
   let at n =
     let uu___2 = FStarC_SMap.try_find pos n in
     match uu___2 with
     | FStar_Pervasives_Native.Some i -> i
     | FStar_Pervasives_Native.None -> Prims.int_zero in
   let succs n =
     let uu___2 = FStarC_SMap.try_find defs n in
     match uu___2 with
     | FStar_Pervasives_Native.None -> []
     | FStar_Pervasives_Native.Some d ->
         let uu___3 =
           let uu___4 = decl_deps d in
           FStarC_List.map
             (fun m ->
                let uu___5 = FStarC_SMap.try_find own m in
                match uu___5 with
                | FStar_Pervasives_Native.Some o -> o
                | FStar_Pervasives_Native.None -> m) uu___4 in
         FStarC_List.filter
           (fun m ->
              let uu___4 = FStarC_SMap.try_find defs m in
              match uu___4 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___5 -> false) uu___3 in
   let index = FStarC_SMap.create (Prims.of_int 50) in
   let low = FStarC_SMap.create (Prims.of_int 50) in
   let onstack = FStarC_SMap.create (Prims.of_int 50) in
   let stack = FStarC_Effect.mk_ref [] in
   let counter = FStarC_Effect.mk_ref Prims.int_zero in
   let comps = FStarC_Effect.mk_ref [] in
   let get m n =
     let uu___2 = FStarC_SMap.try_find m n in
     match uu___2 with
     | FStar_Pervasives_Native.Some i -> i
     | FStar_Pervasives_Native.None -> Prims.int_zero in
   let rec strong v =
     let i = FStarC_Effect.op_Bang counter in
     FStarC_Effect.op_Colon_Equals counter (i + Prims.int_one);
     FStarC_SMap.add index v i;
     FStarC_SMap.add low v i;
     (let uu___6 = let uu___7 = FStarC_Effect.op_Bang stack in v :: uu___7 in
      FStarC_Effect.op_Colon_Equals stack uu___6);
     FStarC_SMap.add onstack v true;
     (let uu___8 = succs v in
      FStarC_List.iter
        (fun w ->
           let uu___9 = FStarC_SMap.try_find index w in
           match uu___9 with
           | FStar_Pervasives_Native.None ->
               (strong w;
                (let uu___11 =
                   let uu___12 = get low v in
                   let uu___13 = get low w in imin uu___12 uu___13 in
                 FStarC_SMap.add low v uu___11))
           | FStar_Pervasives_Native.Some iw ->
               let uu___10 =
                 let uu___11 = FStarC_SMap.try_find onstack w in
                 uu___11 = (FStar_Pervasives_Native.Some true) in
               if uu___10
               then
                 let uu___11 = let uu___12 = get low v in imin uu___12 iw in
                 FStarC_SMap.add low v uu___11
               else ()) uu___8);
     (let uu___8 =
        let uu___9 = get low v in
        let uu___10 = get index v in uu___9 = uu___10 in
      if uu___8
      then
        let rec pop acc st =
          match st with
          | [] -> (acc, [])
          | w::rest ->
              (FStarC_SMap.add onstack w false;
               if w = v then ((w :: acc), rest) else pop (w :: acc) rest) in
        let uu___9 =
          let uu___10 = FStarC_Effect.op_Bang stack in pop [] uu___10 in
        match uu___9 with
        | (comp, rest) ->
            (FStarC_Effect.op_Colon_Equals stack rest;
             (let uu___11 =
                let uu___12 =
                  FStarC_List.sortWith
                    (fun a b ->
                       let uu___13 = at a in
                       let uu___14 = at b in uu___13 - uu___14) comp in
                let uu___13 = FStarC_Effect.op_Bang comps in uu___12 ::
                  uu___13 in
              FStarC_Effect.op_Colon_Equals comps uu___11))
      else ()) in
   FStarC_List.iter
     (fun d ->
        let n = key d in
        let uu___3 =
          let uu___4 = FStarC_SMap.try_find index n in
          match uu___4 with
          | FStar_Pervasives_Native.None -> true
          | uu___5 -> false in
        if uu___3 then strong n else ()) prog;
   (let flags comp =
      match comp with
      | n::[] when
          let uu___3 =
            let uu___4 = succs n in
            FStarC_List.existsb (fun m -> m = n) uu___4 in
          Prims.not uu___3 -> []
      | uu___3 ->
          let uu___4 =
            let uu___5 =
              FStarC_List.collect
                (fun n ->
                   let uu___6 = FStarC_SMap.try_find defs n in
                   match uu___6 with
                   | FStar_Pervasives_Native.Some d ->
                       [FStarC_Custard_Syntax.name_of_decl d]
                   | FStar_Pervasives_Native.None -> []) comp in
            FStarC_Custard_Syntax.Rec uu___5 in
          [uu___4] in
    let retag fs d =
      let keep gs =
        let uu___3 =
          FStarC_List.filter
            (fun f ->
               Prims.not
                 (match f with
                  | FStarC_Custard_Syntax.Rec _0 -> true
                  | uu___4 -> false)) gs in
        FStarC_List.op_At fs uu___3 in
      match d with
      | FStarC_Custard_Syntax.DLet l ->
          let uu___3 =
            let uu___4 = keep l.FStarC_Custard_Syntax.dl_flags in
            {
              FStarC_Custard_Syntax.dl_name =
                (l.FStarC_Custard_Syntax.dl_name);
              FStarC_Custard_Syntax.dl_typars =
                (l.FStarC_Custard_Syntax.dl_typars);
              FStarC_Custard_Syntax.dl_binders =
                (l.FStarC_Custard_Syntax.dl_binders);
              FStarC_Custard_Syntax.dl_ret = (l.FStarC_Custard_Syntax.dl_ret);
              FStarC_Custard_Syntax.dl_eff = (l.FStarC_Custard_Syntax.dl_eff);
              FStarC_Custard_Syntax.dl_body =
                (l.FStarC_Custard_Syntax.dl_body);
              FStarC_Custard_Syntax.dl_flags = uu___4
            } in
          FStarC_Custard_Syntax.DLet uu___3
      | FStarC_Custard_Syntax.DType t ->
          let uu___3 =
            let uu___4 = keep t.FStarC_Custard_Syntax.dt_flags in
            {
              FStarC_Custard_Syntax.dt_name =
                (t.FStarC_Custard_Syntax.dt_name);
              FStarC_Custard_Syntax.dt_params =
                (t.FStarC_Custard_Syntax.dt_params);
              FStarC_Custard_Syntax.dt_body =
                (t.FStarC_Custard_Syntax.dt_body);
              FStarC_Custard_Syntax.dt_flags = uu___4
            } in
          FStarC_Custard_Syntax.DType uu___3
      | FStarC_Custard_Syntax.DExternal x ->
          let uu___3 =
            let uu___4 = keep x.FStarC_Custard_Syntax.dx_flags in
            {
              FStarC_Custard_Syntax.dx_name =
                (x.FStarC_Custard_Syntax.dx_name);
              FStarC_Custard_Syntax.dx_typars =
                (x.FStarC_Custard_Syntax.dx_typars);
              FStarC_Custard_Syntax.dx_ty = (x.FStarC_Custard_Syntax.dx_ty);
              FStarC_Custard_Syntax.dx_target =
                (x.FStarC_Custard_Syntax.dx_target);
              FStarC_Custard_Syntax.dx_header =
                (x.FStarC_Custard_Syntax.dx_header);
              FStarC_Custard_Syntax.dx_flags = uu___4
            } in
          FStarC_Custard_Syntax.DExternal uu___3
      | FStarC_Custard_Syntax.DExn uu___3 -> d in
    let uu___3 =
      let uu___4 = FStarC_Effect.op_Bang comps in FStarC_List.rev uu___4 in
    FStarC_List.collect
      (fun comp ->
         let fs = flags comp in
         FStarC_List.collect
           (fun n ->
              let uu___4 = FStarC_SMap.try_find defs n in
              match uu___4 with
              | FStar_Pervasives_Native.Some d ->
                  let uu___5 = retag fs d in [uu___5]
              | FStar_Pervasives_Native.None -> []) comp) uu___3))
let take (x : FStarC_Custard_Syntax.expr) (c : FStarC_Custard_Syntax.expr)
  (r : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let uu___ = FStarC_Custard_Syntax.is_droppable c in
  if uu___
  then
    {
      FStarC_Custard_Syntax.e = (r.FStarC_Custard_Syntax.e);
      FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
      FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
    }
  else
    {
      FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ESeq (c, r));
      FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
      FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
    }
let rec prune (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let g = prune in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EMatch (s, brs) ->
      let s1 = g s in
      let brs1 = FStarC_List.map prune_branch brs in
      let live =
        FStarC_List.filter
          (fun uu___ ->
             match uu___ with
             | (uu___1, uu___2, b) ->
                 Prims.not
                   (match b.FStarC_Custard_Syntax.e with
                    | FStarC_Custard_Syntax.EAbort _0 -> true
                    | uu___3 -> false)) brs1 in
      (match (live, brs1) with
       | ([], (uu___, uu___1, b)::uu___2) -> take x s1 b
       | ((p, FStar_Pervasives_Native.None, b)::[], uu___) ->
           (match p with
            | FStarC_Custard_Syntax.PWild -> take x s1 b
            | FStarC_Custard_Syntax.PConst uu___1 -> take x s1 b
            | FStarC_Custard_Syntax.PVar v ->
                let uu___1 = occurs v b in
                if uu___1
                then
                  {
                    FStarC_Custard_Syntax.e =
                      (FStarC_Custard_Syntax.ELet
                         (v, (s1.FStarC_Custard_Syntax.ty), s1, b));
                    FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                  }
                else take x s1 b
            | uu___1 ->
                {
                  FStarC_Custard_Syntax.e =
                    (FStarC_Custard_Syntax.EMatch (s1, live));
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                })
       | uu___ ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EMatch
                  (s1,
                    (if (match live with | [] -> true | uu___1 -> false)
                     then brs1
                     else live)));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.EIf (c, a, b) ->
      let c1 = g c in
      let a1 = g a in
      let b1 = g b in
      if
        (match b1.FStarC_Custard_Syntax.e with
         | FStarC_Custard_Syntax.EAbort _0 -> true
         | uu___ -> false) &&
          (Prims.not
             (match a1.FStarC_Custard_Syntax.e with
              | FStarC_Custard_Syntax.EAbort _0 -> true
              | uu___ -> false))
      then take x c1 a1
      else
        if
          (match a1.FStarC_Custard_Syntax.e with
           | FStarC_Custard_Syntax.EAbort _0 -> true
           | uu___ -> false) &&
            (Prims.not
               (match b1.FStarC_Custard_Syntax.e with
                | FStarC_Custard_Syntax.EAbort _0 -> true
                | uu___ -> false))
        then take x c1 b1
        else
          {
            FStarC_Custard_Syntax.e =
              (FStarC_Custard_Syntax.EIf (c1, a1, b1));
            FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
            FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
          }
  | uu___ -> FStarC_Custard_Syntax.map_children g x
and prune_branch (br : FStarC_Custard_Syntax.branch) :
  FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, guard, b) ->
      let uu___1 =
        match guard with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some e ->
            let uu___2 = prune e in FStar_Pervasives_Native.Some uu___2 in
      let uu___2 = prune b in (p, uu___1, uu___2)
let prune_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 = prune dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
type ctor_info =
  {
  ci_owner: FStarC_Custard_Syntax.name ;
  ci_count: Prims.int ;
  ci_params: Prims.string Prims.list ;
  ci_fields: (Prims.string * FStarC_Custard_Syntax.cty) Prims.list ;
  ci_realized: Prims.bool ;
  ci_exn: Prims.bool }
let __proj__Mkctor_info__item__ci_owner (projectee : ctor_info) :
  FStarC_Custard_Syntax.name=
  match projectee with
  | { ci_owner; ci_count; ci_params; ci_fields; ci_realized; ci_exn;_} ->
      ci_owner
let __proj__Mkctor_info__item__ci_count (projectee : ctor_info) : Prims.int=
  match projectee with
  | { ci_owner; ci_count; ci_params; ci_fields; ci_realized; ci_exn;_} ->
      ci_count
let __proj__Mkctor_info__item__ci_params (projectee : ctor_info) :
  Prims.string Prims.list=
  match projectee with
  | { ci_owner; ci_count; ci_params; ci_fields; ci_realized; ci_exn;_} ->
      ci_params
let __proj__Mkctor_info__item__ci_fields (projectee : ctor_info) :
  (Prims.string * FStarC_Custard_Syntax.cty) Prims.list=
  match projectee with
  | { ci_owner; ci_count; ci_params; ci_fields; ci_realized; ci_exn;_} ->
      ci_fields
let __proj__Mkctor_info__item__ci_realized (projectee : ctor_info) :
  Prims.bool=
  match projectee with
  | { ci_owner; ci_count; ci_params; ci_fields; ci_realized; ci_exn;_} ->
      ci_realized
let __proj__Mkctor_info__item__ci_exn (projectee : ctor_info) : Prims.bool=
  match projectee with
  | { ci_owner; ci_count; ci_params; ci_fields; ci_realized; ci_exn;_} ->
      ci_exn
let imported_types : FStarC_Custard_Syntax.decl Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let with_imports (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let uu___ = FStarC_Effect.op_Bang imported_types in
  match uu___ with | [] -> prog | ds -> FStarC_List.op_At ds prog
let ctor_infos (prog : FStarC_Custard_Syntax.program) :
  ctor_info FStarC_SMap.t=
  let m = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType
           { FStarC_Custard_Syntax.dt_name = tn;
             FStarC_Custard_Syntax.dt_params = ps;
             FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TVariant
               cs;
             FStarC_Custard_Syntax.dt_flags = fl;_}
           ->
           let n = FStarC_List.length cs in
           FStarC_List.iter
             (fun uu___1 ->
                match uu___1 with
                | (cn, fs) ->
                    let fs1 =
                      FStarC_List.map
                        (fun uu___2 ->
                           match uu___2 with
                           | (f, c) ->
                               (f,
                                 ((match c with
                                   | FStarC_Custard_Syntax.TInline c1 -> c1
                                   | c1 -> c1)))) fs in
                    let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStarC_Custard_Syntax.has_flag fl
                            FStarC_Custard_Syntax.Realized in
                        if uu___5
                        then
                          let uu___6 =
                            FStarC_Custard_Syntax.has_flag fl
                              FStarC_Custard_Syntax.SourceRecord in
                          Prims.not uu___6
                        else false in
                      {
                        ci_owner = tn;
                        ci_count = n;
                        ci_params = ps;
                        ci_fields = fs1;
                        ci_realized = uu___4;
                        ci_exn = false
                      } in
                    FStarC_SMap.add m uu___2 uu___3) cs
       | FStarC_Custard_Syntax.DType
           { FStarC_Custard_Syntax.dt_name = tn;
             FStarC_Custard_Syntax.dt_params = ps;
             FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TRecord fs;
             FStarC_Custard_Syntax.dt_flags = fl;_}
           ->
           let fs1 =
             FStarC_List.map
               (fun uu___1 ->
                  match uu___1 with
                  | (f, c) ->
                      (f,
                        ((match c with
                          | FStarC_Custard_Syntax.TInline c1 -> c1
                          | c1 -> c1)))) fs in
           let uu___1 = FStarC_Custard_Syntax.string_of_name tn in
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStarC_Custard_Syntax.has_flag fl
                   FStarC_Custard_Syntax.Realized in
               if uu___4
               then
                 let uu___5 =
                   FStarC_Custard_Syntax.has_flag fl
                     FStarC_Custard_Syntax.SourceRecord in
                 Prims.not uu___5
               else false in
             {
               ci_owner = tn;
               ci_count = Prims.int_one;
               ci_params = ps;
               ci_fields = fs1;
               ci_realized = uu___3;
               ci_exn = false
             } in
           FStarC_SMap.add m uu___1 uu___2
       | FStarC_Custard_Syntax.DExn de ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               de.FStarC_Custard_Syntax.de_name in
           let uu___2 =
             let uu___3 =
               FStarC_List.mapi
                 (fun i c ->
                    ((Prims.strcat "_" (Prims.string_of_int i)),
                      (match c with
                       | FStarC_Custard_Syntax.TInline c1 -> c1
                       | c1 -> c1))) de.FStarC_Custard_Syntax.de_args in
             {
               ci_owner = (de.FStarC_Custard_Syntax.de_name);
               ci_count = (Prims.of_int 2);
               ci_params = [];
               ci_fields = uu___3;
               ci_realized = false;
               ci_exn = true
             } in
           FStarC_SMap.add m uu___1 uu___2
       | uu___1 -> ()) prog;
  m
let single_ctor (tbl : ctor_info FStarC_SMap.t)
  (cn : FStarC_Custard_Syntax.name) :
  ctor_info FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
    FStarC_SMap.try_find tbl uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some ci when ci.ci_count = Prims.int_one ->
      FStar_Pervasives_Native.Some ci
  | uu___1 -> FStar_Pervasives_Native.None
let rec dup_ok (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar uu___ -> true
  | FStarC_Custard_Syntax.EConst uu___ -> true
  | FStarC_Custard_Syntax.EQual uu___ -> true
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> dup_ok a
  | uu___ -> false
let rec psub (sm : subst) (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  let g = psub sm in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar v ->
      let uu___ = FStarC_SMap.try_find sm v in
      (match uu___ with
       | FStar_Pervasives_Native.Some e -> e
       | FStar_Pervasives_Native.None -> x)
  | uu___ -> FStarC_Custard_Syntax.map_children g x
let irrefutable (tbl : ctor_info FStarC_SMap.t)
  (p : FStarC_Custard_Syntax.pat) :
  (FStarC_Custard_Syntax.name * ((Prims.string * FStarC_Custard_Syntax.cty) *
    FStarC_Custard_Syntax.pat) Prims.list) FStar_Pervasives_Native.option=
  let plain ps =
    FStarC_List.for_all
      (fun p1 ->
         (match p1 with
          | FStarC_Custard_Syntax.PVar _0 -> true
          | uu___ -> false) ||
           (match p1 with
            | FStarC_Custard_Syntax.PWild -> true
            | uu___ -> false)) ps in
  match p with
  | FStarC_Custard_Syntax.PCtor (cn, ps) ->
      let uu___ = single_ctor tbl cn in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci when
           if
             (Prims.not ci.ci_realized) &&
               ((FStarC_List.length ps) = (FStarC_List.length ci.ci_fields))
           then plain ps
           else false ->
           FStar_Pervasives_Native.Some
             (cn, (FStarC_List.zip ci.ci_fields ps))
       | uu___1 -> FStar_Pervasives_Native.None)
  | FStarC_Custard_Syntax.PRecord (tn, fs) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name tn in
        FStarC_SMap.try_find tbl uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci when
           let uu___1 = FStarC_List.map FStar_Pervasives_Native.snd fs in
           plain uu___1 ->
           let uu___1 =
             let uu___2 =
               FStarC_List.collect
                 (fun uu___3 ->
                    match uu___3 with
                    | (f, q) ->
                        let uu___4 =
                          FStarC_List.tryFind
                            (fun uu___5 ->
                               match uu___5 with | (g, uu___6) -> g = f)
                            ci.ci_fields in
                        (match uu___4 with
                         | FStar_Pervasives_Native.Some fd -> [(fd, q)]
                         | FStar_Pervasives_Native.None -> [])) fs in
             (tn, uu___2) in
           FStar_Pervasives_Native.Some uu___1
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rec depat (tbl : ctor_info FStarC_SMap.t)
  (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let g = depat tbl in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EMatch
      (s, (p, FStar_Pervasives_Native.None, body)::[]) ->
      let s1 = g s in
      let body1 = g body in
      let uu___ = irrefutable tbl p in
      (match uu___ with
       | FStar_Pervasives_Native.Some (cn, fps) ->
           let uu___1 =
             let uu___2 = dup_ok s1 in
             if uu___2
             then (FStar_Pervasives_Native.None, s1)
             else
               (let v = rename "scrut" in
                ((FStar_Pervasives_Native.Some v),
                  {
                    FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EVar v);
                    FStarC_Custard_Syntax.ty = (s1.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
                  })) in
           (match uu___1 with
            | (bound, s') ->
                let sm = FStarC_SMap.create (Prims.of_int 10) in
                let inst ft =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStarC_Custard_Syntax.string_of_name cn in
                      FStarC_SMap.try_find tbl uu___4 in
                    (uu___3, (s1.FStarC_Custard_Syntax.ty)) in
                  match uu___2 with
                  | (FStar_Pervasives_Native.Some ci,
                     FStarC_Custard_Syntax.TApp (uu___3, args)) when
                      (match ci.ci_params with
                       | hd::tl -> true
                       | uu___4 -> false) &&
                        ((FStarC_List.length args) =
                           (FStarC_List.length ci.ci_params))
                      ->
                      FStarC_Custard_Syntax.subst_cty
                        (FStarC_List.zip ci.ci_params args) ft
                  | uu___3 -> ft in
                (FStarC_List.iter
                   (fun uu___3 ->
                      match uu___3 with
                      | ((f, ft), p1) ->
                          (match p1 with
                           | FStarC_Custard_Syntax.PVar v ->
                               let uu___4 =
                                 let uu___5 = inst ft in
                                 FStarC_Custard_Syntax.mk
                                   (FStarC_Custard_Syntax.EProj (s', cn, f))
                                   uu___5 FStarC_Custard_Syntax.E_Pure in
                               FStarC_SMap.add sm v uu___4
                           | uu___4 -> ())) fps;
                 (let body2 = psub sm body1 in
                  match bound with
                  | FStar_Pervasives_Native.None -> body2
                  | FStar_Pervasives_Native.Some v ->
                      {
                        FStarC_Custard_Syntax.e =
                          (FStarC_Custard_Syntax.ELet
                             (v, (s1.FStarC_Custard_Syntax.ty), s1, body2));
                        FStarC_Custard_Syntax.ty =
                          (x.FStarC_Custard_Syntax.ty);
                        FStarC_Custard_Syntax.eff =
                          (x.FStarC_Custard_Syntax.eff)
                      })))
       | FStar_Pervasives_Native.None ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EMatch
                  (s1, [(p, FStar_Pervasives_Native.None, body1)]));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.EDiscrim (e1, cn) ->
      let e11 = g e1 in
      let uu___ = single_ctor tbl cn in
      (match uu___ with
       | FStar_Pervasives_Native.Some uu___1 when
           FStarC_Custard_Syntax.is_pure e11.FStarC_Custard_Syntax.eff ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EConst
                  (FStarC_Custard_Syntax.CBool true));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           }
       | uu___1 ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EDiscrim (e11, cn));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | uu___ -> FStarC_Custard_Syntax.map_children g x
let depat_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let tbl = let uu___ = with_imports prog in ctor_infos uu___ in
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 = depat tbl dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
let eta_ctors (vd : FStarC_Custard_Syntax.verdicts)
  (prog : FStarC_Custard_Syntax.program) : FStarC_Custard_Syntax.program=
  let infos = let uu___ = with_imports prog in ctor_infos uu___ in
  let imported = FStarC_SMap.create (Prims.of_int 20) in
  (let uu___1 = FStarC_Effect.op_Bang imported_types in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DType t ->
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TVariant cs ->
                 FStarC_List.iter
                   (fun uu___2 ->
                      match uu___2 with
                      | (cn, uu___3) ->
                          let uu___4 =
                            FStarC_Custard_Syntax.string_of_name cn in
                          FStarC_SMap.add imported uu___4 ()) cs
             | FStarC_Custard_Syntax.TRecord uu___2 ->
                 let uu___3 =
                   FStarC_Custard_Syntax.string_of_name
                     t.FStarC_Custard_Syntax.dt_name in
                 FStarC_SMap.add imported uu___3 ()
             | uu___2 -> ())
        | uu___2 -> ()) uu___1);
  (let rec unplan pl fs =
     match pl with
     | [] -> []
     | (f, uu___1, FStar_Pervasives_Native.None)::pl1 ->
         (match fs with
          | (uu___2, t)::fs1 ->
              let uu___3 = unplan pl1 fs1 in (f, t) :: uu___3
          | [] -> [])
     | (f, uu___1, FStar_Pervasives_Native.Some ex)::pl1 ->
         let rec drop n l =
           if n <= Prims.int_zero
           then l
           else
             (match l with
              | [] -> []
              | uu___2::l1 -> drop (n - Prims.int_one) l1) in
         let uu___2 =
           unplan pl1
             (drop (FStarC_List.length ex.FStarC_Custard_Syntax.ex_dst) fs) in
         (f, (ex.FStarC_Custard_Syntax.ex_ty)) :: uu___2 in
   let declared cn ci =
     let uu___1 =
       let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
       FStarC_SMap.try_find vd.FStarC_Custard_Syntax.vd_plans uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.Some pl when
         let uu___2 =
           let uu___3 = FStarC_Custard_Syntax.string_of_name cn in
           FStarC_SMap.try_find imported uu___3 in
         match uu___2 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___3 -> false -> unplan pl ci.ci_fields
     | uu___2 -> ci.ci_fields in
   let rec go x =
     let g = go in
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ECtor (cn, es) ->
         let es1 = FStarC_List.map g es in
         let alt =
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.ECtor (cn, es1));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           } in
         let uu___1 =
           let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
           FStarC_SMap.try_find infos uu___2 in
         (match uu___1 with
          | FStar_Pervasives_Native.Some ci ->
              let n = FStarC_List.length es1 in
              let fs = declared cn ci in
              if n >= (FStarC_List.length fs)
              then alt
              else
                (let missing =
                   let uu___2 = FStarC_List.mapi (fun i f -> (i, f)) fs in
                   FStarC_List.collect
                     (fun uu___3 ->
                        match uu___3 with
                        | (i, f) -> if i < n then [] else [f]) uu___2 in
                 let bs =
                   FStarC_List.map
                     (fun uu___2 ->
                        match uu___2 with
                        | (f, t) ->
                            let uu___3 = rename f in
                            {
                              FStarC_Custard_Syntax.b_name = uu___3;
                              FStarC_Custard_Syntax.b_ty = t
                            }) missing in
                 let args =
                   FStarC_List.map
                     (fun b ->
                        FStarC_Custard_Syntax.mk
                          (FStarC_Custard_Syntax.EVar
                             (b.FStarC_Custard_Syntax.b_name))
                          b.FStarC_Custard_Syntax.b_ty
                          FStarC_Custard_Syntax.E_Pure) bs in
                 let res =
                   FStarC_List.fold_right
                     (fun b t ->
                        FStarC_Custard_Syntax.TArrow
                          ((b.FStarC_Custard_Syntax.b_ty),
                            FStarC_Custard_Syntax.E_Pure, t)) bs
                     x.FStarC_Custard_Syntax.ty in
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EFun
                      (bs,
                        {
                          FStarC_Custard_Syntax.e =
                            (FStarC_Custard_Syntax.ECtor
                               (cn, (FStarC_List.op_At es1 args)));
                          FStarC_Custard_Syntax.ty =
                            (alt.FStarC_Custard_Syntax.ty);
                          FStarC_Custard_Syntax.eff =
                            (alt.FStarC_Custard_Syntax.eff)
                        })) res FStarC_Custard_Syntax.E_Pure)
          | FStar_Pervasives_Native.None -> alt)
     | uu___1 -> FStarC_Custard_Syntax.map_children g x in
   FStarC_List.map
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl ->
            let uu___1 =
              let uu___2 = go dl.FStarC_Custard_Syntax.dl_body in
              {
                FStarC_Custard_Syntax.dl_name =
                  (dl.FStarC_Custard_Syntax.dl_name);
                FStarC_Custard_Syntax.dl_typars =
                  (dl.FStarC_Custard_Syntax.dl_typars);
                FStarC_Custard_Syntax.dl_binders =
                  (dl.FStarC_Custard_Syntax.dl_binders);
                FStarC_Custard_Syntax.dl_ret =
                  (dl.FStarC_Custard_Syntax.dl_ret);
                FStarC_Custard_Syntax.dl_eff =
                  (dl.FStarC_Custard_Syntax.dl_eff);
                FStarC_Custard_Syntax.dl_body = uu___2;
                FStarC_Custard_Syntax.dl_flags =
                  (dl.FStarC_Custard_Syntax.dl_flags)
              } in
            FStarC_Custard_Syntax.DLet uu___1
        | d1 -> d1) prog)
let records (vd : FStarC_Custard_Syntax.verdicts)
  (prog : FStarC_Custard_Syntax.program) : FStarC_Custard_Syntax.program=
  let fields = FStarC_SMap.create (Prims.of_int 100) in
  (let uu___1 = with_imports prog in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DType t ->
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TRecord fs ->
                 let uu___2 =
                   FStarC_Custard_Syntax.string_of_name
                     t.FStarC_Custard_Syntax.dt_name in
                 let uu___3 = FStarC_List.map FStar_Pervasives_Native.fst fs in
                 FStarC_SMap.add fields uu___2 uu___3
             | FStarC_Custard_Syntax.TVariant ((uu___2, fs)::[]) ->
                 let uu___3 =
                   FStarC_Custard_Syntax.string_of_name
                     t.FStarC_Custard_Syntax.dt_name in
                 let uu___4 = FStarC_List.map FStar_Pervasives_Native.fst fs in
                 FStarC_SMap.add fields uu___3 uu___4
             | uu___2 -> ())
        | uu___2 -> ()) uu___1);
  (let as_record cn =
     let uu___1 =
       let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
       FStarC_SMap.try_find vd.FStarC_Custard_Syntax.vd_records uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some tn ->
         let uu___2 =
           let uu___3 = FStarC_Custard_Syntax.string_of_name tn in
           FStarC_SMap.try_find fields uu___3 in
         (match uu___2 with
          | FStar_Pervasives_Native.Some fs ->
              FStar_Pervasives_Native.Some (tn, fs)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None) in
   let rec go x =
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ECtor (cn, es) ->
         let es1 = FStarC_List.map go es in
         let uu___1 = as_record cn in
         (match uu___1 with
          | FStar_Pervasives_Native.Some (tn, fs) ->
              if (FStarC_List.length fs) <> (FStarC_List.length es1)
              then
                let uu___2 =
                  let uu___3 = FStarC_Custard_Syntax.string_of_name cn in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length fs) in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length es1) in
                  FStarC_Format.fmt3
                    "custard records: %s expects %s fields, applied to %s"
                    uu___3 uu___4 uu___5 in
                FStarC_Effect.failwith uu___2
              else
                {
                  FStarC_Custard_Syntax.e =
                    (FStarC_Custard_Syntax.ERecord
                       (tn, (FStarC_List.zip fs es1)));
                  FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                  FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
                }
          | FStar_Pervasives_Native.None ->
              {
                FStarC_Custard_Syntax.e =
                  (FStarC_Custard_Syntax.ECtor (cn, es1));
                FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
              })
     | FStarC_Custard_Syntax.EProj (e1, n, f) ->
         let e11 = go e1 in
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 = as_record n in
               match uu___4 with
               | FStar_Pervasives_Native.Some (tn, uu___5) -> tn
               | FStar_Pervasives_Native.None -> n in
             (e11, uu___3, f) in
           FStarC_Custard_Syntax.EProj uu___2 in
         {
           FStarC_Custard_Syntax.e = uu___1;
           FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
           FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
         }
     | FStarC_Custard_Syntax.EMatch (s, brs) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = go s in
             let uu___4 = FStarC_List.map go_branch brs in (uu___3, uu___4) in
           FStarC_Custard_Syntax.EMatch uu___2 in
         {
           FStarC_Custard_Syntax.e = uu___1;
           FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
           FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
         }
     | FStarC_Custard_Syntax.ETry (s, brs) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = go s in
             let uu___4 = FStarC_List.map go_branch brs in (uu___3, uu___4) in
           FStarC_Custard_Syntax.ETry uu___2 in
         {
           FStarC_Custard_Syntax.e = uu___1;
           FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
           FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
         }
     | uu___1 -> FStarC_Custard_Syntax.map_children go x
   and go_pat p =
     match p with
     | FStarC_Custard_Syntax.PCtor (cn, ps) ->
         let ps1 = FStarC_List.map go_pat ps in
         let uu___1 = as_record cn in
         (match uu___1 with
          | FStar_Pervasives_Native.Some (tn, fs) ->
              if (FStarC_List.length fs) <> (FStarC_List.length ps1)
              then
                let uu___2 =
                  let uu___3 = FStarC_Custard_Syntax.string_of_name cn in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length fs) in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                      (FStarC_List.length ps1) in
                  FStarC_Format.fmt3
                    "custard records pat: %s expects %s fields, matched %s"
                    uu___3 uu___4 uu___5 in
                FStarC_Effect.failwith uu___2
              else
                FStarC_Custard_Syntax.PRecord (tn, (FStarC_List.zip fs ps1))
          | FStar_Pervasives_Native.None ->
              FStarC_Custard_Syntax.PCtor (cn, ps1))
     | FStarC_Custard_Syntax.PRecord (n, fs) ->
         let uu___1 =
           let uu___2 =
             FStarC_List.map
               (fun uu___3 ->
                  match uu___3 with
                  | (f, q) -> let uu___4 = go_pat q in (f, uu___4)) fs in
           (n, uu___2) in
         FStarC_Custard_Syntax.PRecord uu___1
     | FStarC_Custard_Syntax.PTuple ps ->
         let uu___1 = FStarC_List.map go_pat ps in
         FStarC_Custard_Syntax.PTuple uu___1
     | FStarC_Custard_Syntax.POr ps ->
         let uu___1 = FStarC_List.map go_pat ps in
         FStarC_Custard_Syntax.POr uu___1
     | p1 -> p1
   and go_branch br =
     let uu___1 = br in
     match uu___1 with
     | (p, gd, b) ->
         let uu___2 = go_pat p in
         let uu___3 =
           match gd with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some g ->
               let uu___4 = go g in FStar_Pervasives_Native.Some uu___4 in
         let uu___4 = go b in (uu___2, uu___3, uu___4) in
   FStarC_List.map
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl ->
            let uu___1 =
              let uu___2 = go dl.FStarC_Custard_Syntax.dl_body in
              {
                FStarC_Custard_Syntax.dl_name =
                  (dl.FStarC_Custard_Syntax.dl_name);
                FStarC_Custard_Syntax.dl_typars =
                  (dl.FStarC_Custard_Syntax.dl_typars);
                FStarC_Custard_Syntax.dl_binders =
                  (dl.FStarC_Custard_Syntax.dl_binders);
                FStarC_Custard_Syntax.dl_ret =
                  (dl.FStarC_Custard_Syntax.dl_ret);
                FStarC_Custard_Syntax.dl_eff =
                  (dl.FStarC_Custard_Syntax.dl_eff);
                FStarC_Custard_Syntax.dl_body = uu___2;
                FStarC_Custard_Syntax.dl_flags =
                  (dl.FStarC_Custard_Syntax.dl_flags)
              } in
            FStarC_Custard_Syntax.DLet uu___1
        | FStarC_Custard_Syntax.DType t ->
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TVariant ((cn, fs)::[]) ->
                 let uu___1 = as_record cn in
                 (match uu___1 with
                  | FStar_Pervasives_Native.Some uu___2 ->
                      FStarC_Custard_Syntax.DType
                        {
                          FStarC_Custard_Syntax.dt_name =
                            (t.FStarC_Custard_Syntax.dt_name);
                          FStarC_Custard_Syntax.dt_params =
                            (t.FStarC_Custard_Syntax.dt_params);
                          FStarC_Custard_Syntax.dt_body =
                            (FStarC_Custard_Syntax.TRecord fs);
                          FStarC_Custard_Syntax.dt_flags =
                            (t.FStarC_Custard_Syntax.dt_flags)
                        }
                  | FStar_Pervasives_Native.None -> d)
             | uu___1 -> d)
        | d1 -> d1) prog)
let ex_key (ex : FStarC_Custard_Syntax.expansion) :
  FStarC_Custard_Syntax.name=
  match ex.FStarC_Custard_Syntax.ex_ctor with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None -> ex.FStarC_Custard_Syntax.ex_type
let pure_ (e : FStarC_Custard_Syntax.expr') (t : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.expr=
  FStarC_Custard_Syntax.mk e t FStarC_Custard_Syntax.E_Pure
let ex_build (ex : FStarC_Custard_Syntax.expansion)
  (vs : FStarC_Custard_Syntax.expr Prims.list) : FStarC_Custard_Syntax.expr=
  match ex.FStarC_Custard_Syntax.ex_ctor with
  | FStar_Pervasives_Native.Some c ->
      pure_ (FStarC_Custard_Syntax.ECtor (c, vs))
        ex.FStarC_Custard_Syntax.ex_ty
  | FStar_Pervasives_Native.None ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_List.map FStar_Pervasives_Native.fst
                ex.FStarC_Custard_Syntax.ex_src in
            FStarC_List.zip uu___3 vs in
          ((ex.FStarC_Custard_Syntax.ex_type), uu___2) in
        FStarC_Custard_Syntax.ERecord uu___1 in
      pure_ uu___ ex.FStarC_Custard_Syntax.ex_ty
let ex_take (ex : FStarC_Custard_Syntax.expansion)
  (e : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr Prims.list FStar_Pervasives_Native.option=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ECtor (c, vs) ->
      let uu___ =
        let uu___1 =
          match ex.FStarC_Custard_Syntax.ex_ctor with
          | FStar_Pervasives_Native.Some rc ->
              let uu___2 = FStarC_Custard_Syntax.string_of_name c in
              let uu___3 = FStarC_Custard_Syntax.string_of_name rc in
              uu___2 = uu___3
          | FStar_Pervasives_Native.None -> false in
        if uu___1
        then
          (FStarC_List.length vs) =
            (FStarC_List.length ex.FStarC_Custard_Syntax.ex_src)
        else false in
      if uu___
      then FStar_Pervasives_Native.Some vs
      else FStar_Pervasives_Native.None
  | FStarC_Custard_Syntax.ERecord (tn, fs) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name tn in
        let uu___2 =
          FStarC_Custard_Syntax.string_of_name
            ex.FStarC_Custard_Syntax.ex_type in
        uu___1 = uu___2 in
      if uu___
      then
        let uu___1 =
          FStarC_List.map
            (fun uu___2 ->
               match uu___2 with
               | (g, gt) ->
                   let uu___3 =
                     FStarC_List.tryFind
                       (fun uu___4 ->
                          match uu___4 with | (h, uu___5) -> h = g) fs in
                   (match uu___3 with
                    | FStar_Pervasives_Native.Some (uu___4, v) -> v
                    | FStar_Pervasives_Native.None ->
                        FStarC_Custard_Syntax.mk FStarC_Custard_Syntax.EAny
                          gt FStarC_Custard_Syntax.E_Pure))
            ex.FStarC_Custard_Syntax.ex_src in
        FStar_Pervasives_Native.Some uu___1
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let strip_inline (c : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.cty=
  match c with | FStarC_Custard_Syntax.TInline c1 -> c1 | c1 -> c1
let rec only_projected (v : Prims.string) (x : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  let g = only_projected v in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar w -> w <> v
  | FStarC_Custard_Syntax.EProj (e1, uu___, uu___1) ->
      (match e1.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EVar w -> if w = v then true else g e1
       | uu___2 -> g e1)
  | uu___ -> FStarC_Custard_Syntax.for_all_children g x
let rec rebinds (v : Prims.string) (x : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  let g = rebinds v in
  let rec pv p =
    match p with
    | FStarC_Custard_Syntax.PVar w -> w = v
    | FStarC_Custard_Syntax.PCtor (uu___, ps) -> FStarC_List.existsb pv ps
    | FStarC_Custard_Syntax.PTuple ps -> FStarC_List.existsb pv ps
    | FStarC_Custard_Syntax.POr ps -> FStarC_List.existsb pv ps
    | FStarC_Custard_Syntax.PRecord (uu___, fs) ->
        FStarC_List.existsb
          (fun uu___1 -> match uu___1 with | (uu___2, q) -> pv q) fs
    | uu___ -> false in
  let br r =
    let uu___ = r in
    match uu___ with
    | (p, gd, b) ->
        let uu___1 =
          let uu___2 = pv p in
          if uu___2
          then true
          else
            (match gd with
             | FStar_Pervasives_Native.Some gd1 -> g gd1
             | FStar_Pervasives_Native.None -> false) in
        if uu___1 then true else g b in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet (w, uu___, e1, e2) ->
      let uu___1 = if w = v then true else g e1 in
      if uu___1 then true else g e2
  | FStarC_Custard_Syntax.EFun (bs, b) ->
      let uu___ =
        FStarC_List.existsb (fun b1 -> b1.FStarC_Custard_Syntax.b_name = v)
          bs in
      if uu___ then true else g b
  | FStarC_Custard_Syntax.EMatch (sc, brs) ->
      let uu___ = g sc in if uu___ then true else FStarC_List.existsb br brs
  | FStarC_Custard_Syntax.ETry (a, brs) ->
      let uu___ = g a in if uu___ then true else FStarC_List.existsb br brs
  | uu___ -> FStarC_Custard_Syntax.exists_child g x
let rec unbuild (infos : ctor_info FStarC_SMap.t)
  (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let g = unbuild infos in
  let pick fs f =
    let uu___ =
      FStarC_List.for_all
        (fun uu___1 ->
           match uu___1 with
           | (h, e) ->
               (h = f) ||
                 (FStarC_Custard_Syntax.is_pure e.FStarC_Custard_Syntax.eff))
        fs in
    if uu___
    then
      let uu___1 =
        FStarC_List.tryFind
          (fun uu___2 -> match uu___2 with | (h, uu___3) -> h = f) fs in
      match uu___1 with
      | FStar_Pervasives_Native.Some (uu___2, e) ->
          FStar_Pervasives_Native.Some e
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.None in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EProj (e1, n, f) ->
      let e11 = g e1 in
      let alt =
        {
          FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EProj (e11, n, f));
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        } in
      (match e11.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
           let uu___1 = pick fs f in
           (match uu___1 with
            | FStar_Pervasives_Native.Some e -> e
            | FStar_Pervasives_Native.None -> alt)
       | FStarC_Custard_Syntax.ECtor (cn, es) ->
           let uu___ =
             let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
             FStarC_SMap.try_find infos uu___1 in
           (match uu___ with
            | FStar_Pervasives_Native.Some ci ->
                if
                  (FStarC_List.length es) <>
                    (FStarC_List.length ci.ci_fields)
                then alt
                else
                  (let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         FStarC_List.map FStar_Pervasives_Native.fst
                           ci.ci_fields in
                       FStarC_List.zip uu___3 es in
                     pick uu___2 f in
                   match uu___1 with
                   | FStar_Pervasives_Native.Some e -> e
                   | FStar_Pervasives_Native.None -> alt)
            | FStar_Pervasives_Native.None -> alt)
       | uu___ -> alt)
  | FStarC_Custard_Syntax.ELet (v, t, rhs, b) ->
      let rhs1 = g rhs in
      let b1 = g b in
      let alt =
        {
          FStarC_Custard_Syntax.e =
            (FStarC_Custard_Syntax.ELet (v, t, rhs1, b1));
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        } in
      let fields =
        match rhs1.FStarC_Custard_Syntax.e with
        | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
            FStar_Pervasives_Native.Some fs
        | FStarC_Custard_Syntax.ECtor (cn, es) ->
            let uu___ =
              let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
              FStarC_SMap.try_find infos uu___1 in
            (match uu___ with
             | FStar_Pervasives_Native.Some ci ->
                 if
                   (FStarC_List.length es) =
                     (FStarC_List.length ci.ci_fields)
                 then
                   let uu___1 =
                     let uu___2 =
                       FStarC_List.map FStar_Pervasives_Native.fst
                         ci.ci_fields in
                     FStarC_List.zip uu___2 es in
                   FStar_Pervasives_Native.Some uu___1
                 else FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        | uu___ -> FStar_Pervasives_Native.None in
      (match fields with
       | FStar_Pervasives_Native.Some fs when
           let uu___ =
             let uu___1 =
               FStarC_List.for_all
                 (fun uu___2 -> match uu___2 with | (uu___3, e) -> reeval e)
                 fs in
             if uu___1 then only_projected v b1 else false in
           if uu___
           then let uu___1 = rebinds v b1 in Prims.not uu___1
           else false ->
           let sm = FStarC_SMap.create Prims.int_one in
           (FStarC_SMap.add sm v rhs1; (let uu___1 = psub sm b1 in g uu___1))
       | uu___ -> alt)
  | uu___ -> FStarC_Custard_Syntax.map_children g x
let inline_fields (vd : FStarC_Custard_Syntax.verdicts)
  (prog : FStarC_Custard_Syntax.program) : FStarC_Custard_Syntax.program=
  let uu___ =
    let uu___1 = FStarC_SMap.keys vd.FStarC_Custard_Syntax.vd_plans in
    uu___1 = [] in
  if uu___
  then prog
  else
    (let plan cn =
       let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
       FStarC_SMap.try_find vd.FStarC_Custard_Syntax.vd_plans uu___1 in
     let rec go x =
       match x.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.ECtor (cn, es) ->
           let es1 = FStarC_List.map go es in
           let alt =
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.ECtor (cn, es1));
               FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
             } in
           let uu___1 = plan cn in
           (match uu___1 with
            | FStar_Pervasives_Native.Some fs ->
                if (FStarC_List.length es1) <> (FStarC_List.length fs)
                then alt
                else
                  (let uu___2 =
                     FStarC_List.fold_left2
                       (fun uu___3 e uu___4 ->
                          match (uu___3, uu___4) with
                          | ((binds, acc), (uu___5, uu___6, ex)) ->
                              (match ex with
                               | FStar_Pervasives_Native.None ->
                                   (binds, (FStarC_List.op_At acc [e]))
                               | FStar_Pervasives_Native.Some ex1 ->
                                   let uu___7 = ex_take ex1 e in
                                   (match uu___7 with
                                    | FStar_Pervasives_Native.Some vs ->
                                        (binds, (FStarC_List.op_At acc vs))
                                    | FStar_Pervasives_Native.None ->
                                        let uu___8 =
                                          let uu___9 = dup_ok e in
                                          if uu___9
                                          then (binds, e)
                                          else
                                            (let n = rename "fld" in
                                             ((FStarC_List.op_At binds
                                                 [(n,
                                                    (e.FStarC_Custard_Syntax.ty),
                                                    e)]),
                                               (FStarC_Custard_Syntax.mk
                                                  (FStarC_Custard_Syntax.EVar
                                                     n)
                                                  e.FStarC_Custard_Syntax.ty
                                                  FStarC_Custard_Syntax.E_Pure))) in
                                        (match uu___8 with
                                         | (binds1, v) ->
                                             let uu___9 =
                                               let uu___10 =
                                                 FStarC_List.map
                                                   (fun uu___11 ->
                                                      match uu___11 with
                                                      | (g, gt) ->
                                                          pure_
                                                            (FStarC_Custard_Syntax.EProj
                                                               (v,
                                                                 (ex_key ex1),
                                                                 g)) gt)
                                                   ex1.FStarC_Custard_Syntax.ex_src in
                                               FStarC_List.op_At acc uu___10 in
                                             (binds1, uu___9))))) ([], [])
                       es1 fs in
                   match uu___2 with
                   | (binds, args) ->
                       let body =
                         {
                           FStarC_Custard_Syntax.e =
                             (FStarC_Custard_Syntax.ECtor (cn, args));
                           FStarC_Custard_Syntax.ty =
                             (x.FStarC_Custard_Syntax.ty);
                           FStarC_Custard_Syntax.eff =
                             (x.FStarC_Custard_Syntax.eff)
                         } in
                       FStarC_List.fold_right
                         (fun uu___3 acc ->
                            match uu___3 with
                            | (n, t, e) ->
                                {
                                  FStarC_Custard_Syntax.e =
                                    (FStarC_Custard_Syntax.ELet
                                       (n, t, e, acc));
                                  FStarC_Custard_Syntax.ty =
                                    (acc.FStarC_Custard_Syntax.ty);
                                  FStarC_Custard_Syntax.eff =
                                    (acc.FStarC_Custard_Syntax.eff)
                                }) binds body)
            | FStar_Pervasives_Native.None -> alt)
       | FStarC_Custard_Syntax.EProj (e1, cn, f) ->
           let e11 = go e1 in
           let alt =
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.EProj (e11, cn, f));
               FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
             } in
           let uu___1 = plan cn in
           (match uu___1 with
            | FStar_Pervasives_Native.Some fs ->
                let uu___2 =
                  FStarC_List.tryFind
                    (fun uu___3 ->
                       match uu___3 with | (g, uu___4, uu___5) -> g = f) fs in
                (match uu___2 with
                 | FStar_Pervasives_Native.Some
                     (uu___3, f', FStar_Pervasives_Native.None) ->
                     {
                       FStarC_Custard_Syntax.e =
                         (FStarC_Custard_Syntax.EProj (e11, cn, f'));
                       FStarC_Custard_Syntax.ty =
                         (x.FStarC_Custard_Syntax.ty);
                       FStarC_Custard_Syntax.eff =
                         (x.FStarC_Custard_Syntax.eff)
                     }
                 | FStar_Pervasives_Native.Some
                     (uu___3, uu___4, FStar_Pervasives_Native.Some ex) ->
                     let uu___5 =
                       let uu___6 = dup_ok e11 in
                       if uu___6
                       then (FStar_Pervasives_Native.None, e11)
                       else
                         (let n = rename "whole" in
                          ((FStar_Pervasives_Native.Some n),
                            (FStarC_Custard_Syntax.mk
                               (FStarC_Custard_Syntax.EVar n)
                               e11.FStarC_Custard_Syntax.ty
                               FStarC_Custard_Syntax.E_Pure))) in
                     (match uu___5 with
                      | (bind, v) ->
                          let vs =
                            FStarC_List.map
                              (fun uu___6 ->
                                 match uu___6 with
                                 | (g, gt) ->
                                     pure_
                                       (FStarC_Custard_Syntax.EProj
                                          (v, cn, g)) gt)
                              ex.FStarC_Custard_Syntax.ex_dst in
                          let b = ex_build ex vs in
                          (match bind with
                           | FStar_Pervasives_Native.None -> b
                           | FStar_Pervasives_Native.Some n ->
                               {
                                 FStarC_Custard_Syntax.e =
                                   (FStarC_Custard_Syntax.ELet
                                      (n, (e11.FStarC_Custard_Syntax.ty),
                                        e11, b));
                                 FStarC_Custard_Syntax.ty =
                                   (b.FStarC_Custard_Syntax.ty);
                                 FStarC_Custard_Syntax.eff =
                                   (b.FStarC_Custard_Syntax.eff)
                               }))
                 | FStar_Pervasives_Native.None -> alt)
            | FStar_Pervasives_Native.None -> alt)
       | FStarC_Custard_Syntax.EMatch (s, brs) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = go s in
               let uu___4 = FStarC_List.map go_branch brs in (uu___3, uu___4) in
             FStarC_Custard_Syntax.EMatch uu___2 in
           {
             FStarC_Custard_Syntax.e = uu___1;
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           }
       | FStarC_Custard_Syntax.ETry (s, brs) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = go s in
               let uu___4 = FStarC_List.map go_branch brs in (uu___3, uu___4) in
             FStarC_Custard_Syntax.ETry uu___2 in
           {
             FStarC_Custard_Syntax.e = uu___1;
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           }
       | uu___1 -> FStarC_Custard_Syntax.map_children go x
     and go_branch br =
       let uu___1 = br in
       match uu___1 with
       | (p, gd, b) ->
           let sm = FStarC_SMap.create (Prims.of_int 10) in
           let lets = FStarC_Effect.mk_ref [] in
           let free v =
             let uses =
               let uu___2 = count v b in
               let uu___3 =
                 match gd with
                 | FStar_Pervasives_Native.None -> Prims.int_zero
                 | FStar_Pervasives_Native.Some g -> count v g in
               uu___2 + uu___3 in
             if uses <= Prims.int_one
             then true
             else
               (let uu___2 = only_projected v b in
                if uu___2
                then
                  match gd with
                  | FStar_Pervasives_Native.None -> true
                  | FStar_Pervasives_Native.Some g -> only_projected v g
                else false) in
           let rec go_pat p1 =
             match p1 with
             | FStarC_Custard_Syntax.PCtor (cn, ps) ->
                 let ps1 = FStarC_List.map go_pat ps in
                 let uu___2 = plan cn in
                 (match uu___2 with
                  | FStar_Pervasives_Native.Some fs ->
                      if (FStarC_List.length ps1) <> (FStarC_List.length fs)
                      then FStarC_Custard_Syntax.PCtor (cn, ps1)
                      else
                        (let uu___3 =
                           let uu___4 =
                             FStarC_List.fold_left2
                               (fun acc p2 uu___5 ->
                                  match uu___5 with
                                  | (uu___6, uu___7, ex) ->
                                      (match ex with
                                       | FStar_Pervasives_Native.None ->
                                           FStarC_List.op_At acc [p2]
                                       | FStar_Pervasives_Native.Some ex1 ->
                                           (match p2 with
                                            | FStarC_Custard_Syntax.PCtor
                                                (uu___8, qs) ->
                                                FStarC_List.op_At acc qs
                                            | FStarC_Custard_Syntax.PWild ->
                                                let uu___8 =
                                                  FStarC_List.map
                                                    (fun uu___9 ->
                                                       FStarC_Custard_Syntax.PWild)
                                                    ex1.FStarC_Custard_Syntax.ex_dst in
                                                FStarC_List.op_At acc uu___8
                                            | FStarC_Custard_Syntax.PVar v ->
                                                let ns =
                                                  FStarC_List.map
                                                    (fun uu___8 ->
                                                       match uu___8 with
                                                       | (g, gt) ->
                                                           let uu___9 =
                                                             rename g in
                                                           (uu___9, gt))
                                                    ex1.FStarC_Custard_Syntax.ex_src in
                                                let e =
                                                  let uu___8 =
                                                    FStarC_List.map
                                                      (fun uu___9 ->
                                                         match uu___9 with
                                                         | (n, t) ->
                                                             FStarC_Custard_Syntax.mk
                                                               (FStarC_Custard_Syntax.EVar
                                                                  n) t
                                                               FStarC_Custard_Syntax.E_Pure)
                                                      ns in
                                                  ex_build ex1 uu___8 in
                                                ((let uu___9 = free v in
                                                  if uu___9
                                                  then FStarC_SMap.add sm v e
                                                  else
                                                    (let uu___10 =
                                                       let uu___11 =
                                                         FStarC_Effect.op_Bang
                                                           lets in
                                                       FStarC_List.op_At
                                                         uu___11
                                                         [(v,
                                                            (ex1.FStarC_Custard_Syntax.ex_ty),
                                                            e)] in
                                                     FStarC_Effect.op_Colon_Equals
                                                       lets uu___10));
                                                 (let uu___9 =
                                                    FStarC_List.map
                                                      (fun uu___10 ->
                                                         match uu___10 with
                                                         | (n, uu___11) ->
                                                             FStarC_Custard_Syntax.PVar
                                                               n) ns in
                                                  FStarC_List.op_At acc
                                                    uu___9))
                                            | uu___8 ->
                                                FStarC_List.op_At acc [p2])))
                               [] ps1 fs in
                           (cn, uu___4) in
                         FStarC_Custard_Syntax.PCtor uu___3)
                  | FStar_Pervasives_Native.None ->
                      FStarC_Custard_Syntax.PCtor (cn, ps1))
             | FStarC_Custard_Syntax.PRecord (n, fs) ->
                 let uu___2 =
                   let uu___3 =
                     FStarC_List.map
                       (fun uu___4 ->
                          match uu___4 with
                          | (f, q) -> let uu___5 = go_pat q in (f, uu___5))
                       fs in
                   (n, uu___3) in
                 FStarC_Custard_Syntax.PRecord uu___2
             | FStarC_Custard_Syntax.PTuple ps ->
                 let uu___2 = FStarC_List.map go_pat ps in
                 FStarC_Custard_Syntax.PTuple uu___2
             | FStarC_Custard_Syntax.POr ps ->
                 let uu___2 = FStarC_List.map go_pat ps in
                 FStarC_Custard_Syntax.POr uu___2
             | p2 -> p2 in
           let p1 = go_pat p in
           let gsm = FStarC_SMap.create (Prims.of_int 10) in
           ((let uu___3 = FStarC_SMap.keys sm in
             FStarC_List.iter
               (fun k ->
                  let uu___4 = FStarC_SMap.try_find sm k in
                  match uu___4 with
                  | FStar_Pervasives_Native.Some e -> FStarC_SMap.add gsm k e
                  | FStar_Pervasives_Native.None -> ()) uu___3);
            (let uu___4 = FStarC_Effect.op_Bang lets in
             FStarC_List.iter
               (fun uu___5 ->
                  match uu___5 with | (v, t, e) -> FStarC_SMap.add gsm v e)
               uu___4);
            (let gd1 =
               match gd with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g ->
                   let uu___4 = let uu___5 = psub gsm g in go uu___5 in
                   FStar_Pervasives_Native.Some uu___4 in
             let b1 = let uu___4 = psub sm b in go uu___4 in
             let b2 =
               let uu___4 = FStarC_Effect.op_Bang lets in
               FStarC_List.fold_right
                 (fun uu___5 acc ->
                    match uu___5 with
                    | (v, t, e) ->
                        {
                          FStarC_Custard_Syntax.e =
                            (FStarC_Custard_Syntax.ELet (v, t, e, acc));
                          FStarC_Custard_Syntax.ty =
                            (acc.FStarC_Custard_Syntax.ty);
                          FStarC_Custard_Syntax.eff =
                            (acc.FStarC_Custard_Syntax.eff)
                        }) uu___4 b1 in
             (p1, gd1, b2))) in
     FStarC_List.map
       (fun d ->
          match d with
          | FStarC_Custard_Syntax.DLet dl ->
              let uu___1 =
                let uu___2 = go dl.FStarC_Custard_Syntax.dl_body in
                {
                  FStarC_Custard_Syntax.dl_name =
                    (dl.FStarC_Custard_Syntax.dl_name);
                  FStarC_Custard_Syntax.dl_typars =
                    (dl.FStarC_Custard_Syntax.dl_typars);
                  FStarC_Custard_Syntax.dl_binders =
                    (dl.FStarC_Custard_Syntax.dl_binders);
                  FStarC_Custard_Syntax.dl_ret =
                    (dl.FStarC_Custard_Syntax.dl_ret);
                  FStarC_Custard_Syntax.dl_eff =
                    (dl.FStarC_Custard_Syntax.dl_eff);
                  FStarC_Custard_Syntax.dl_body = uu___2;
                  FStarC_Custard_Syntax.dl_flags =
                    (dl.FStarC_Custard_Syntax.dl_flags)
                } in
              FStarC_Custard_Syntax.DLet uu___1
          | FStarC_Custard_Syntax.DType t ->
              (match t.FStarC_Custard_Syntax.dt_body with
               | FStarC_Custard_Syntax.TVariant cs ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         FStarC_List.map
                           (fun uu___4 ->
                              match uu___4 with
                              | (cn, fs) ->
                                  let uu___5 = plan cn in
                                  (match uu___5 with
                                   | FStar_Pervasives_Native.Some pl ->
                                       if
                                         (FStarC_List.length pl) <>
                                           (FStarC_List.length fs)
                                       then
                                         let uu___6 =
                                           FStarC_List.map
                                             (fun uu___7 ->
                                                match uu___7 with
                                                | (f, c) ->
                                                    (f, (strip_inline c))) fs in
                                         (cn, uu___6)
                                       else
                                         (let uu___6 =
                                            FStarC_List.collect
                                              (fun uu___7 ->
                                                 match uu___7 with
                                                 | ((uu___8, c),
                                                    (uu___9, f', ex)) ->
                                                     (match ex with
                                                      | FStar_Pervasives_Native.Some
                                                          ex1 ->
                                                          ex1.FStarC_Custard_Syntax.ex_dst
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          [(f',
                                                             (strip_inline c))]))
                                              (FStarC_List.zip fs pl) in
                                          (cn, uu___6))
                                   | FStar_Pervasives_Native.None ->
                                       let uu___6 =
                                         FStarC_List.map
                                           (fun uu___7 ->
                                              match uu___7 with
                                              | (f, c) ->
                                                  (f, (strip_inline c))) fs in
                                       (cn, uu___6))) cs in
                       FStarC_Custard_Syntax.TVariant uu___3 in
                     {
                       FStarC_Custard_Syntax.dt_name =
                         (t.FStarC_Custard_Syntax.dt_name);
                       FStarC_Custard_Syntax.dt_params =
                         (t.FStarC_Custard_Syntax.dt_params);
                       FStarC_Custard_Syntax.dt_body = uu___2;
                       FStarC_Custard_Syntax.dt_flags =
                         (t.FStarC_Custard_Syntax.dt_flags)
                     } in
                   FStarC_Custard_Syntax.DType uu___1
               | FStarC_Custard_Syntax.TRecord fs ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         FStarC_List.map
                           (fun uu___4 ->
                              match uu___4 with
                              | (f, c) -> (f, (strip_inline c))) fs in
                       FStarC_Custard_Syntax.TRecord uu___3 in
                     {
                       FStarC_Custard_Syntax.dt_name =
                         (t.FStarC_Custard_Syntax.dt_name);
                       FStarC_Custard_Syntax.dt_params =
                         (t.FStarC_Custard_Syntax.dt_params);
                       FStarC_Custard_Syntax.dt_body = uu___2;
                       FStarC_Custard_Syntax.dt_flags =
                         (t.FStarC_Custard_Syntax.dt_flags)
                     } in
                   FStarC_Custard_Syntax.DType uu___1
               | uu___1 -> d)
          | d1 -> d1) prog)
let unbuild_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let infos = let uu___ = with_imports prog in ctor_infos uu___ in
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 = unbuild infos dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
let rec refutable (infos : ctor_info FStarC_SMap.t)
  (p : FStarC_Custard_Syntax.pat) : Prims.bool=
  match p with
  | FStarC_Custard_Syntax.PVar uu___ -> false
  | FStarC_Custard_Syntax.PWild -> false
  | FStarC_Custard_Syntax.PConst uu___ -> true
  | FStarC_Custard_Syntax.POr uu___ -> true
  | FStarC_Custard_Syntax.PTuple ps ->
      FStarC_List.existsb (refutable infos) ps
  | FStarC_Custard_Syntax.PRecord (uu___, fps) ->
      FStarC_List.existsb
        (fun uu___1 -> match uu___1 with | (uu___2, q) -> refutable infos q)
        fps
  | FStarC_Custard_Syntax.PCtor (cn, ps) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
        FStarC_SMap.try_find infos uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci when ci.ci_count = Prims.int_one ->
           FStarC_List.existsb (refutable infos) ps
       | uu___1 -> true)
let inst_fields (ci : ctor_info)
  (sc : FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option) :
  (Prims.string * FStarC_Custard_Syntax.cty) Prims.list=
  match sc with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TApp (uu___, args))
      when (FStarC_List.length args) = (FStarC_List.length ci.ci_params) ->
      let sub1 = FStarC_List.zip ci.ci_params args in
      FStarC_List.map
        (fun uu___1 ->
           match uu___1 with
           | (f, t) ->
               let uu___2 = FStarC_Custard_Syntax.subst_cty sub1 t in
               (f, uu___2)) ci.ci_fields
  | uu___ -> ci.ci_fields
let tuple_fields
  (sc : FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option)
  (ps : FStarC_Custard_Syntax.pat Prims.list) :
  FStarC_Custard_Syntax.cty Prims.list=
  match sc with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TTuple ts) when
      (FStarC_List.length ts) = (FStarC_List.length ps) -> ts
  | uu___ ->
      FStarC_List.map (fun uu___1 -> FStarC_Custard_Syntax.TVar "?") ps
let rec splits_refutably (infos : ctor_info FStarC_SMap.t)
  (sc : FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option)
  (p : FStarC_Custard_Syntax.pat) : Prims.bool=
  let simple q =
    (match q with | FStarC_Custard_Syntax.PVar _0 -> true | uu___ -> false)
      ||
      (match q with | FStarC_Custard_Syntax.PWild -> true | uu___ -> false) in
  let field t q =
    let uu___ =
      if
        (match t with | FStarC_Custard_Syntax.TAny -> true | uu___1 -> false)
          && (Prims.not (simple q))
      then refutable infos q
      else false in
    if uu___
    then true
    else splits_refutably infos (FStar_Pervasives_Native.Some t) q in
  let many ts ps =
    FStarC_List.existsb (fun uu___ -> match uu___ with | (t, q) -> field t q)
      (FStarC_List.zip ts ps) in
  match p with
  | FStarC_Custard_Syntax.PCtor (cn, ps) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
        FStarC_SMap.try_find infos uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci when
           (FStarC_List.length ci.ci_fields) = (FStarC_List.length ps) ->
           let uu___1 =
             let uu___2 = inst_fields ci sc in
             FStarC_List.map FStar_Pervasives_Native.snd uu___2 in
           many uu___1 ps
       | uu___1 -> false)
  | FStarC_Custard_Syntax.PRecord (tn, fps) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name tn in
        FStarC_SMap.try_find infos uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci ->
           let fs = inst_fields ci sc in
           FStarC_List.existsb
             (fun uu___1 ->
                match uu___1 with
                | (f, q) ->
                    let uu___2 =
                      FStarC_List.tryFind
                        (fun uu___3 ->
                           match uu___3 with | (g, uu___4) -> g = f) fs in
                    (match uu___2 with
                     | FStar_Pervasives_Native.Some (uu___3, t) -> field t q
                     | FStar_Pervasives_Native.None ->
                         field (FStarC_Custard_Syntax.TVar "?") q)) fps
       | FStar_Pervasives_Native.None -> false)
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = tuple_fields sc ps in many uu___ ps
  | FStarC_Custard_Syntax.POr uu___ -> false
  | FStarC_Custard_Syntax.PVar uu___ -> false
  | FStarC_Custard_Syntax.PWild -> false
  | FStarC_Custard_Syntax.PConst uu___ -> false
let rec split_any (infos : ctor_info FStarC_SMap.t)
  (fb : FStarC_Custard_Syntax.expr FStar_Pervasives_Native.option)
  (sc : FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option)
  (p : FStarC_Custard_Syntax.pat) (body : FStarC_Custard_Syntax.expr) :
  (FStarC_Custard_Syntax.pat * FStarC_Custard_Syntax.expr)=
  let simple p1 =
    (match p1 with | FStarC_Custard_Syntax.PVar _0 -> true | uu___ -> false)
      ||
      (match p1 with | FStarC_Custard_Syntax.PWild -> true | uu___ -> false) in
  let field t p1 body1 =
    if
      (match t with | FStarC_Custard_Syntax.TAny -> true | uu___ -> false) &&
        (Prims.not (simple p1))
    then
      let v = rename "any" in
      let sc1 =
        FStarC_Custard_Syntax.mk
          (FStarC_Custard_Syntax.ECoerce
             ((FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EVar v)
                 FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Pure),
               FStarC_Custard_Syntax.TAny)) FStarC_Custard_Syntax.TAny
          FStarC_Custard_Syntax.E_Pure in
      let need = refutable infos p1 in
      let uu___ =
        split_any infos fb
          (FStar_Pervasives_Native.Some FStarC_Custard_Syntax.TAny) p1 body1 in
      match uu___ with
      | (p2, body2) ->
          let brs = (p2, FStar_Pervasives_Native.None, body2) ::
            (match fb with
             | FStar_Pervasives_Native.Some e when need ->
                 [(FStarC_Custard_Syntax.PWild, FStar_Pervasives_Native.None,
                    e)]
             | uu___1 -> []) in
          ((FStarC_Custard_Syntax.PVar v),
            {
              FStarC_Custard_Syntax.e =
                (FStarC_Custard_Syntax.EMatch (sc1, brs));
              FStarC_Custard_Syntax.ty = (body2.FStarC_Custard_Syntax.ty);
              FStarC_Custard_Syntax.eff = (body2.FStarC_Custard_Syntax.eff)
            })
    else split_any infos fb (FStar_Pervasives_Native.Some t) p1 body1 in
  let many ts ps body1 =
    FStarC_List.fold_right
      (fun uu___ uu___1 ->
         match (uu___, uu___1) with
         | ((t, p1), (ps1, body2)) ->
             let uu___2 = field t p1 body2 in
             (match uu___2 with | (p2, body3) -> ((p2 :: ps1), body3)))
      (FStarC_List.zip ts ps) ([], body1) in
  match p with
  | FStarC_Custard_Syntax.PCtor (cn, ps) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name cn in
        FStarC_SMap.try_find infos uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci when
           (FStarC_List.length ci.ci_fields) = (FStarC_List.length ps) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = inst_fields ci sc in
               FStarC_List.map FStar_Pervasives_Native.snd uu___3 in
             many uu___2 ps body in
           (match uu___1 with
            | (ps1, body1) ->
                ((FStarC_Custard_Syntax.PCtor (cn, ps1)), body1))
       | uu___1 -> (p, body))
  | FStarC_Custard_Syntax.PRecord (tn, fps) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name tn in
        FStarC_SMap.try_find infos uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some ci ->
           let fs = inst_fields ci sc in
           let ts =
             FStarC_List.map
               (fun uu___1 ->
                  match uu___1 with
                  | (f, uu___2) ->
                      let uu___3 =
                        FStarC_List.tryFind
                          (fun uu___4 ->
                             match uu___4 with | (g, uu___5) -> g = f) fs in
                      (match uu___3 with
                       | FStar_Pervasives_Native.Some (uu___4, t) -> t
                       | FStar_Pervasives_Native.None ->
                           FStarC_Custard_Syntax.TVar "?")) fps in
           let uu___1 =
             let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd fps in
             many ts uu___2 body in
           (match uu___1 with
            | (ps, body1) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStarC_List.map FStar_Pervasives_Native.fst fps in
                      FStarC_List.zip uu___5 ps in
                    (tn, uu___4) in
                  FStarC_Custard_Syntax.PRecord uu___3 in
                (uu___2, body1))
       | FStar_Pervasives_Native.None -> (p, body))
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = let uu___1 = tuple_fields sc ps in many uu___1 ps body in
      (match uu___ with
       | (ps1, body1) -> ((FStarC_Custard_Syntax.PTuple ps1), body1))
  | FStarC_Custard_Syntax.POr uu___ -> (p, body)
  | FStarC_Custard_Syntax.PVar uu___ -> (p, body)
  | FStarC_Custard_Syntax.PWild -> (p, body)
  | FStarC_Custard_Syntax.PConst uu___ -> (p, body)
let rec split_any_expr (infos : ctor_info FStarC_SMap.t)
  (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let g = split_any_expr infos in
  let br sc fb b0 =
    let uu___ = b0 in
    match uu___ with
    | (p, gd, b) ->
        let b1 = g b in
        (match gd with
         | FStar_Pervasives_Native.Some gd1 ->
             let uu___1 =
               let uu___2 = g gd1 in FStar_Pervasives_Native.Some uu___2 in
             (p, uu___1, b1)
         | FStar_Pervasives_Native.None ->
             let uu___1 = split_any infos fb sc p b1 in
             (match uu___1 with
              | (p1, b2) -> (p1, FStar_Pervasives_Native.None, b2))) in
  let branches sc x1 brs =
    let scty = FStar_Pervasives_Native.Some (sc.FStarC_Custard_Syntax.ty) in
    let needed =
      FStarC_List.existsb
        (fun uu___ ->
           match uu___ with
           | (p, gd, uu___1) ->
               if
                 (match gd with
                  | FStar_Pervasives_Native.None -> true
                  | uu___2 -> false)
               then splits_refutably infos scty p
               else false) brs in
    if Prims.not needed
    then
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.map (br scty FStar_Pervasives_Native.None) brs in
          (sc, uu___2) in
        FStarC_Custard_Syntax.EMatch uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
    else
      (let v = rename "sc" in
       let sv uu___ =
         FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EVar v)
           sc.FStarC_Custard_Syntax.ty FStarC_Custard_Syntax.E_Pure in
       let rec go bs =
         match bs with
         | [] -> []
         | b0::rest ->
             let rest1 = go rest in
             let fb =
               match rest1 with
               | [] -> FStar_Pervasives_Native.None
               | uu___ ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = let uu___4 = sv () in (uu___4, rest1) in
                       FStarC_Custard_Syntax.EMatch uu___3 in
                     FStarC_Custard_Syntax.mk uu___2
                       x1.FStarC_Custard_Syntax.ty
                       x1.FStarC_Custard_Syntax.eff in
                   FStar_Pervasives_Native.Some uu___1 in
             let uu___ = br scty fb b0 in uu___ :: rest1 in
       let brs1 = go brs in
       let uu___ =
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 = let uu___5 = sv () in (uu___5, brs1) in
               FStarC_Custard_Syntax.EMatch uu___4 in
             FStarC_Custard_Syntax.mk uu___3 x1.FStarC_Custard_Syntax.ty
               x1.FStarC_Custard_Syntax.eff in
           (v, (sc.FStarC_Custard_Syntax.ty), sc, uu___2) in
         FStarC_Custard_Syntax.ELet uu___1 in
       {
         FStarC_Custard_Syntax.e = uu___;
         FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
         FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
       }) in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EMatch (s, brs) ->
      let uu___ = g s in branches uu___ x brs
  | FStarC_Custard_Syntax.ETry (s, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = g s in
          let uu___3 =
            FStarC_List.map
              (br (FStar_Pervasives_Native.Some FStarC_Custard_Syntax.TExn)
                 FStar_Pervasives_Native.None) brs in
          (uu___2, uu___3) in
        FStarC_Custard_Syntax.ETry uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
      }
  | uu___ -> FStarC_Custard_Syntax.map_children g x
let split_any_decls (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let infos = let uu___ = with_imports prog in ctor_infos uu___ in
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 =
               split_any_expr infos dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
let rec unit_args_expr (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  let g = unit_args_expr in
  let arg acc e =
    let e1 = g e in
    if
      Prims.not
        (match e1.FStarC_Custard_Syntax.ty with
         | FStarC_Custard_Syntax.TUnit -> true
         | uu___ -> false)
    then e1
    else
      (match e1.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CUnit) -> e1
       | FStarC_Custard_Syntax.EAbort uu___ -> e1
       | uu___ ->
           if FStarC_Custard_Syntax.is_pure e1.FStarC_Custard_Syntax.eff
           then
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.EConst FStarC_Custard_Syntax.CUnit);
               FStarC_Custard_Syntax.ty = (e1.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (e1.FStarC_Custard_Syntax.eff)
             }
           else
             (let v =
                let uu___1 = FStarC_GenSym.next_id () in
                FStarC_Custard_Syntax.uniq "tmp" uu___1 in
              (let uu___2 =
                 let uu___3 = FStarC_Effect.op_Bang acc in
                 (v, (e1.FStarC_Custard_Syntax.ty), e1) :: uu___3 in
               FStarC_Effect.op_Colon_Equals acc uu___2);
              {
                FStarC_Custard_Syntax.e =
                  (FStarC_Custard_Syntax.EConst FStarC_Custard_Syntax.CUnit);
                FStarC_Custard_Syntax.ty = (e1.FStarC_Custard_Syntax.ty);
                FStarC_Custard_Syntax.eff = FStarC_Custard_Syntax.E_Pure
              })) in
  let with_hoists k =
    let acc = FStarC_Effect.mk_ref [] in
    let body = k acc in
    let uu___ = FStarC_Effect.op_Bang acc in
    FStarC_List.fold_left
      (fun body1 uu___1 ->
         match uu___1 with
         | (v, t, e) ->
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.ELet (v, t, e, body1));
               FStarC_Custard_Syntax.ty = (body1.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (body1.FStarC_Custard_Syntax.eff)
             }) body uu___ in
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EApp (h, es) ->
      with_hoists
        (fun acc ->
           let h1 = g h in
           let es1 = FStarC_List.map (arg acc) es in
           {
             FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.EApp (h1, es1));
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.ETuple es ->
      with_hoists
        (fun acc ->
           let uu___ =
             let uu___1 = FStarC_List.map (arg acc) es in
             FStarC_Custard_Syntax.ETuple uu___1 in
           {
             FStarC_Custard_Syntax.e = uu___;
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.EOp (o, es) ->
      with_hoists
        (fun acc ->
           let uu___ =
             let uu___1 =
               let uu___2 = FStarC_List.map (arg acc) es in (o, uu___2) in
             FStarC_Custard_Syntax.EOp uu___1 in
           {
             FStarC_Custard_Syntax.e = uu___;
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.ECtor (n, es) ->
      with_hoists
        (fun acc ->
           let uu___ =
             let uu___1 =
               let uu___2 = FStarC_List.map (arg acc) es in (n, uu___2) in
             FStarC_Custard_Syntax.ECtor uu___1 in
           {
             FStarC_Custard_Syntax.e = uu___;
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.ERecord (n, fs) ->
      with_hoists
        (fun acc ->
           let uu___ =
             let uu___1 =
               let uu___2 =
                 FStarC_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (f, e) -> let uu___4 = arg acc e in (f, uu___4)) fs in
               (n, uu___2) in
             FStarC_Custard_Syntax.ERecord uu___1 in
           {
             FStarC_Custard_Syntax.e = uu___;
             FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
           })
  | uu___ -> FStarC_Custard_Syntax.map_children g x
let unit_args (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl ->
           let uu___ =
             let uu___1 = unit_args_expr dl.FStarC_Custard_Syntax.dl_body in
             {
               FStarC_Custard_Syntax.dl_name =
                 (dl.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (dl.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (dl.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (dl.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (dl.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body = uu___1;
               FStarC_Custard_Syntax.dl_flags =
                 (dl.FStarC_Custard_Syntax.dl_flags)
             } in
           FStarC_Custard_Syntax.DLet uu___
       | d1 -> d1) prog
let rec cty_mismatch (a : FStarC_Custard_Syntax.cty)
  (b : FStarC_Custard_Syntax.cty) : Prims.bool=
  match (a, b) with
  | (FStarC_Custard_Syntax.TAny, FStarC_Custard_Syntax.TAny) -> false
  | (FStarC_Custard_Syntax.TAny, uu___) -> true
  | (uu___, FStarC_Custard_Syntax.TAny) -> true
  | (FStarC_Custard_Syntax.TArrow (a1, uu___, a2),
     FStarC_Custard_Syntax.TArrow (b1, uu___1, b2)) ->
      let uu___2 = cty_mismatch a1 b1 in
      if uu___2 then true else cty_mismatch a2 b2
  | (FStarC_Custard_Syntax.TApp (n, xs), FStarC_Custard_Syntax.TApp (m, ys))
      ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        let uu___2 = FStarC_Custard_Syntax.string_of_name m in
        uu___1 = uu___2 in
      if uu___ then ctys_mismatch xs ys else false
  | (FStarC_Custard_Syntax.TBuf x, FStarC_Custard_Syntax.TBuf y) ->
      cty_mismatch x y
  | (FStarC_Custard_Syntax.TRef x, FStarC_Custard_Syntax.TRef y) ->
      cty_mismatch x y
  | (FStarC_Custard_Syntax.TInline x, FStarC_Custard_Syntax.TInline y) ->
      cty_mismatch x y
  | (FStarC_Custard_Syntax.TTuple xs, FStarC_Custard_Syntax.TTuple ys) ->
      ctys_mismatch xs ys
  | uu___ -> false
and ctys_mismatch (xs : FStarC_Custard_Syntax.cty Prims.list)
  (ys : FStarC_Custard_Syntax.cty Prims.list) : Prims.bool=
  match (xs, ys) with
  | ([], []) -> false
  | (x::xs1, y::ys1) ->
      let uu___ = cty_mismatch x y in
      if uu___ then true else ctys_mismatch xs1 ys1
  | uu___ -> false
let rec over_applied (n : Prims.int) (c : FStarC_Custard_Syntax.cty) :
  Prims.bool=
  if n <= Prims.int_zero
  then false
  else
    (match c with
     | FStarC_Custard_Syntax.TArrow (uu___, uu___1, r) ->
         over_applied (n - Prims.int_one) r
     | FStarC_Custard_Syntax.TAny -> true
     | uu___ -> false)
let rec peel_arrows (n : Prims.int) (c : FStarC_Custard_Syntax.cty) :
  (FStarC_Custard_Syntax.cty Prims.list * FStarC_Custard_Syntax.cty)
    FStar_Pervasives_Native.option=
  if n <= Prims.int_zero
  then FStar_Pervasives_Native.Some ([], c)
  else
    (match c with
     | FStarC_Custard_Syntax.TArrow (a, uu___, r) ->
         (match peel_arrows (n - Prims.int_one) r with
          | FStar_Pervasives_Native.Some (ps, res) ->
              FStar_Pervasives_Native.Some ((a :: ps), res)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | uu___ -> FStar_Pervasives_Native.None)
let rec arrows (ts : FStarC_Custard_Syntax.cty Prims.list)
  (res : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.cty=
  match ts with
  | [] -> res
  | t::ts1 ->
      FStarC_Custard_Syntax.TArrow
        (t, FStarC_Custard_Syntax.E_Pure, (arrows ts1 res))
type cenv =
  FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option FStarC_SMap.t
let coerce_prog (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let all = with_imports prog in
  let infos = ctor_infos all in
  let tparams = FStarC_SMap.create (Prims.of_int 50) in
  let sigs = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType dt ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               dt.FStarC_Custard_Syntax.dt_name in
           FStarC_SMap.add tparams uu___1 dt.FStarC_Custard_Syntax.dt_params
       | FStarC_Custard_Syntax.DLet dl ->
           let rec build bs =
             match bs with
             | [] -> dl.FStarC_Custard_Syntax.dl_ret
             | b::bs1 ->
                 FStarC_Custard_Syntax.TArrow
                   ((b.FStarC_Custard_Syntax.b_ty),
                     FStarC_Custard_Syntax.E_Pure, (build bs1)) in
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               dl.FStarC_Custard_Syntax.dl_name in
           FStarC_SMap.add sigs uu___1
             ((dl.FStarC_Custard_Syntax.dl_typars),
               (build dl.FStarC_Custard_Syntax.dl_binders))
       | FStarC_Custard_Syntax.DExternal dx ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               dx.FStarC_Custard_Syntax.dx_name in
           FStarC_SMap.add sigs uu___1
             ((dx.FStarC_Custard_Syntax.dx_typars),
               (dx.FStarC_Custard_Syntax.dx_ty))
       | FStarC_Custard_Syntax.DExn uu___1 -> ()) all;
  (let params_of n =
     let uu___1 =
       let uu___2 = FStarC_Custard_Syntax.string_of_name n in
       FStarC_SMap.try_find tparams uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.Some ps -> ps
     | FStar_Pervasives_Native.None -> [] in
   let sig_of n targs =
     let uu___1 =
       let uu___2 = FStarC_Custard_Syntax.string_of_name n in
       FStarC_SMap.try_find sigs uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (ps, t) ->
         if (FStarC_List.length ps) = (FStarC_List.length targs)
         then
           let uu___2 =
             FStarC_Custard_Syntax.subst_cty (FStarC_List.zip ps targs) t in
           FStar_Pervasives_Native.Some uu___2
         else FStar_Pervasives_Native.Some t in
   let owner_of key =
     let uu___1 = FStarC_SMap.try_find infos key in
     match uu___1 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some ci ->
         if ci.ci_exn
         then FStar_Pervasives_Native.Some FStarC_Custard_Syntax.TExn
         else
           (let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = params_of ci.ci_owner in
                  FStarC_List.map (fun uu___6 -> FStarC_Custard_Syntax.TAny)
                    uu___5 in
                ((ci.ci_owner), uu___4) in
              FStarC_Custard_Syntax.TApp uu___3 in
            FStar_Pervasives_Native.Some uu___2) in
   let fields_of1 key owner =
     let uu___1 = FStarC_SMap.try_find infos key in
     match uu___1 with
     | FStar_Pervasives_Native.None -> []
     | FStar_Pervasives_Native.Some ci ->
         let ps = params_of ci.ci_owner in
         let args =
           match owner with
           | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TApp
               (uu___2, args1)) -> args1
           | uu___2 -> [] in
         if
           ((FStarC_List.length ps) = (FStarC_List.length args)) &&
             ((match ps with | hd::tl -> true | uu___2 -> false))
         then
           let s = FStarC_List.zip ps args in
           FStarC_List.map
             (fun uu___2 ->
                match uu___2 with
                | (f, c) ->
                    let uu___3 = FStarC_Custard_Syntax.subst_cty s c in
                    (f, uu___3)) ci.ci_fields
         else ci.ci_fields in
   let field_of key owner f =
     let uu___1 =
       let uu___2 = fields_of1 key owner in
       FStarC_List.tryFind
         (fun uu___3 -> match uu___3 with | (g, uu___4) -> g = f) uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.Some (uu___2, t) ->
         FStar_Pervasives_Native.Some t
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
   let prims id =
     FStarC_Custard_Syntax.TApp
       ({
          FStarC_Custard_Syntax.ns = ["Prims"];
          FStarC_Custard_Syntax.id = id;
          FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
        }, []) in
   let ty_of_const c =
     match c with
     | FStarC_Custard_Syntax.CUnit -> FStarC_Custard_Syntax.TUnit
     | FStarC_Custard_Syntax.CBool uu___1 -> prims "bool"
     | FStarC_Custard_Syntax.CInt
         (uu___1, uu___2, FStar_Pervasives_Native.None) -> prims "int"
     | FStarC_Custard_Syntax.CInt
         (uu___1, uu___2, FStar_Pervasives_Native.Some sw) ->
         FStarC_Custard_Syntax.TInt sw
     | FStarC_Custard_Syntax.CFloat (uu___1, fw) ->
         FStarC_Custard_Syntax.TFloat fw
     | FStarC_Custard_Syntax.CChar uu___1 -> prims "char"
     | FStarC_Custard_Syntax.CString uu___1 -> prims "string" in
   let rec scrutinee_of brs =
     match brs with
     | [] -> FStar_Pervasives_Native.None
     | (p, uu___1, uu___2)::brs1 ->
         (match p with
          | FStarC_Custard_Syntax.PCtor (n, uu___3) ->
              let uu___4 = FStarC_Custard_Syntax.string_of_name n in
              owner_of uu___4
          | FStarC_Custard_Syntax.PRecord (n, uu___3) ->
              let uu___4 = FStarC_Custard_Syntax.string_of_name n in
              owner_of uu___4
          | FStarC_Custard_Syntax.PConst c ->
              FStar_Pervasives_Native.Some (ty_of_const c)
          | uu___3 -> scrutinee_of brs1) in
   let rec has_any c =
     match c with
     | FStarC_Custard_Syntax.TAny -> true
     | FStarC_Custard_Syntax.TArrow (a, uu___1, b) ->
         let uu___2 = has_any a in if uu___2 then true else has_any b
     | FStarC_Custard_Syntax.TApp (uu___1, args) ->
         FStarC_List.existsb has_any args
     | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.existsb has_any cs
     | FStarC_Custard_Syntax.TBuf c1 -> has_any c1
     | FStarC_Custard_Syntax.TRef c1 -> has_any c1
     | FStarC_Custard_Syntax.TInline c1 -> has_any c1
     | FStarC_Custard_Syntax.TVar uu___1 -> false
     | FStarC_Custard_Syntax.TInt uu___1 -> false
     | FStarC_Custard_Syntax.TFloat uu___1 -> false
     | FStarC_Custard_Syntax.TUnit -> false
     | FStarC_Custard_Syntax.TExn -> false
     | FStarC_Custard_Syntax.TConst uu___1 -> false in
   let trust c =
     let uu___1 = has_any c in
     if uu___1
     then FStar_Pervasives_Native.None
     else FStar_Pervasives_Native.Some c in
   let concrete_shape x =
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ECtor uu___1 -> true
     | FStarC_Custard_Syntax.ERecord uu___1 -> true
     | FStarC_Custard_Syntax.ETuple uu___1 -> true
     | FStarC_Custard_Syntax.EConst uu___1 -> true
     | FStarC_Custard_Syntax.EFun uu___1 -> true
     | FStarC_Custard_Syntax.EOp uu___1 -> true
     | uu___1 -> false in
   let lookup env v = FStarC_SMap.try_find env v in
   let extend env v t =
     let env' = FStarC_SMap.copy env in FStarC_SMap.add env' v t; env' in
   let rec bind_pat env sc p =
     match p with
     | FStarC_Custard_Syntax.PWild -> env
     | FStarC_Custard_Syntax.PConst uu___1 -> env
     | FStarC_Custard_Syntax.PVar v -> extend env v sc
     | FStarC_Custard_Syntax.POr ps ->
         FStarC_List.fold_left (fun env1 p1 -> bind_pat env1 sc p1) env ps
     | FStarC_Custard_Syntax.PTuple ps ->
         let ts =
           match sc with
           | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TTuple ts1)
               when (FStarC_List.length ts1) = (FStarC_List.length ps) ->
               FStarC_List.map
                 (fun uu___1 -> FStar_Pervasives_Native.Some uu___1) ts1
           | uu___1 ->
               FStarC_List.map (fun uu___2 -> FStar_Pervasives_Native.None)
                 ps in
         FStarC_List.fold_left
           (fun env1 uu___1 ->
              match uu___1 with | (t, p1) -> bind_pat env1 t p1) env
           (FStarC_List.zip ts ps)
     | FStarC_Custard_Syntax.PCtor (n, ps) ->
         let fs =
           let uu___1 = FStarC_Custard_Syntax.string_of_name n in
           fields_of1 uu___1 sc in
         if (FStarC_List.length fs) = (FStarC_List.length ps)
         then
           FStarC_List.fold_left
             (fun env1 uu___1 ->
                match uu___1 with
                | ((uu___2, t), p1) ->
                    bind_pat env1 (FStar_Pervasives_Native.Some t) p1) env
             (FStarC_List.zip fs ps)
         else
           FStarC_List.fold_left
             (fun env1 p1 -> bind_pat env1 FStar_Pervasives_Native.None p1)
             env ps
     | FStarC_Custard_Syntax.PRecord (n, fps) ->
         FStarC_List.fold_left
           (fun env1 uu___1 ->
              match uu___1 with
              | (f, p1) ->
                  let uu___2 =
                    let uu___3 = FStarC_Custard_Syntax.string_of_name n in
                    field_of uu___3 sc f in
                  bind_pat env1 uu___2 p1) env fps in
   let rec unify_cty p a acc =
     match (p, a) with
     | (FStarC_Custard_Syntax.TVar v, uu___1) ->
         let uu___2 =
           FStarC_List.existsb
             (fun uu___3 -> match uu___3 with | (w, uu___4) -> w = v) acc in
         if uu___2 then acc else (v, a) :: acc
     | (FStarC_Custard_Syntax.TArrow (p1, uu___1, p2),
        FStarC_Custard_Syntax.TArrow (a1, uu___2, a2)) ->
         let uu___3 = unify_cty p1 a1 acc in unify_cty p2 a2 uu___3
     | (FStarC_Custard_Syntax.TApp (n, ps), FStarC_Custard_Syntax.TApp
        (m, qs)) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = FStarC_Custard_Syntax.string_of_name n in
             let uu___4 = FStarC_Custard_Syntax.string_of_name m in
             uu___3 = uu___4 in
           if uu___2
           then (FStarC_List.length ps) = (FStarC_List.length qs)
           else false in
         if uu___1 then unify_ctys ps qs acc else acc
     | (FStarC_Custard_Syntax.TTuple ps, FStarC_Custard_Syntax.TTuple qs) ->
         if (FStarC_List.length ps) = (FStarC_List.length qs)
         then unify_ctys ps qs acc
         else acc
     | (FStarC_Custard_Syntax.TBuf p1, FStarC_Custard_Syntax.TBuf a1) ->
         unify_cty p1 a1 acc
     | (FStarC_Custard_Syntax.TRef p1, FStarC_Custard_Syntax.TRef a1) ->
         unify_cty p1 a1 acc
     | (FStarC_Custard_Syntax.TInline p1, FStarC_Custard_Syntax.TInline a1)
         -> unify_cty p1 a1 acc
     | uu___1 -> acc
   and unify_ctys ps qs acc =
     match (ps, qs) with
     | (p::ps1, q::qs1) ->
         let uu___1 = unify_cty p q acc in unify_ctys ps1 qs1 uu___1
     | uu___1 -> acc in
   let rec infer env x =
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.EVar v ->
         let uu___1 = lookup env v in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t -> t
          | FStar_Pervasives_Native.None -> trust x.FStarC_Custard_Syntax.ty)
     | FStarC_Custard_Syntax.EQual (n, targs) ->
         let uu___1 = sig_of n targs in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | FStar_Pervasives_Native.None -> trust x.FStarC_Custard_Syntax.ty)
     | FStarC_Custard_Syntax.ECast (uu___1, t) ->
         FStar_Pervasives_Native.Some t
     | FStarC_Custard_Syntax.ECoerce (uu___1, t) ->
         FStar_Pervasives_Native.Some t
     | FStarC_Custard_Syntax.EApp (h, es) ->
         let uu___1 = infer env h in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t ->
              (match peel_arrows (FStarC_List.length es) t with
               | FStar_Pervasives_Native.Some (ps, res) ->
                   let sub1 =
                     FStarC_List.fold_left2
                       (fun acc p e ->
                          let uu___2 = infer env e in
                          match uu___2 with
                          | FStar_Pervasives_Native.Some a ->
                              unify_cty p a acc
                          | FStar_Pervasives_Native.None -> acc) [] ps es in
                   let uu___2 = FStarC_Custard_Syntax.subst_cty sub1 res in
                   FStar_Pervasives_Native.Some uu___2
               | FStar_Pervasives_Native.None ->
                   trust x.FStarC_Custard_Syntax.ty)
          | FStar_Pervasives_Native.None -> trust x.FStarC_Custard_Syntax.ty)
     | FStarC_Custard_Syntax.EProj (e1, n, f) ->
         let uu___1 =
           let uu___2 = FStarC_Custard_Syntax.string_of_name n in
           let uu___3 = infer env e1 in field_of uu___2 uu___3 f in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | FStar_Pervasives_Native.None -> trust x.FStarC_Custard_Syntax.ty)
     | FStarC_Custard_Syntax.ELet (v, t, e1, e2) ->
         let uu___1 = let uu___2 = binding env t e1 in extend env v uu___2 in
         infer uu___1 e2
     | FStarC_Custard_Syntax.ESeq (uu___1, b) -> infer env b
     | FStarC_Custard_Syntax.EMatch (sc, (p, uu___1, b)::uu___2) ->
         (match b.FStarC_Custard_Syntax.e with
          | FStarC_Custard_Syntax.EVar uu___3 ->
              let uu___4 = let uu___5 = infer env sc in bind_pat env uu___5 p in
              infer uu___4 b
          | FStarC_Custard_Syntax.EProj uu___3 ->
              let uu___4 = let uu___5 = infer env sc in bind_pat env uu___5 p in
              infer uu___4 b
          | FStarC_Custard_Syntax.EQual uu___3 ->
              let uu___4 = let uu___5 = infer env sc in bind_pat env uu___5 p in
              infer uu___4 b
          | uu___3 -> trust x.FStarC_Custard_Syntax.ty)
     | uu___1 -> trust x.FStarC_Custard_Syntax.ty
   and binding env t e1 =
     let uu___1 = trust t in
     match uu___1 with
     | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
     | FStar_Pervasives_Native.None -> infer env e1 in
   let first a b =
     match a with
     | FStar_Pervasives_Native.Some uu___1 -> a
     | FStar_Pervasives_Native.None -> b in
   let cond_ty =
     FStar_Pervasives_Native.Some
       (FStarC_Custard_Syntax.TApp
          ({
             FStarC_Custard_Syntax.ns = ["Prims"];
             FStarC_Custard_Syntax.id = "bool";
             FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
           }, [])) in
   let pushes_down x =
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ELet uu___1 -> true
     | FStarC_Custard_Syntax.ESeq uu___1 -> true
     | FStarC_Custard_Syntax.EIf uu___1 -> true
     | FStarC_Custard_Syntax.EMatch uu___1 -> true
     | FStarC_Custard_Syntax.ETry uu___1 -> true
     | uu___1 -> false in
   let coerce x t =
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ECoerce (e1, uu___1) ->
         FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.ECoerce (e1, t)) t
           x.FStarC_Custard_Syntax.eff
     | uu___1 ->
         FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.ECoerce (x, t)) t
           x.FStarC_Custard_Syntax.eff in
   let rec check env exp x =
     let x1 = go env exp x in
     let uu___1 =
       if
         match exp with
         | FStar_Pervasives_Native.Some v -> true
         | uu___2 -> false
       then pushes_down x1
       else false in
     if uu___1
     then x1
     else
       (let uu___2 = let uu___3 = infer env x1 in (exp, uu___3) in
        match uu___2 with
        | (FStar_Pervasives_Native.Some e, FStar_Pervasives_Native.Some t) ->
            let uu___3 = cty_mismatch t e in
            if uu___3 then coerce x1 e else x1
        | (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TAny),
           FStar_Pervasives_Native.None) ->
            let uu___3 = concrete_shape x1 in
            if uu___3 then coerce x1 FStarC_Custard_Syntax.TAny else x1
        | uu___3 -> x1)
   and go env exp x =
     let same e' =
       {
         FStarC_Custard_Syntax.e = e';
         FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
         FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
       } in
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.EConst uu___1 -> x
     | FStarC_Custard_Syntax.EVar uu___1 -> x
     | FStarC_Custard_Syntax.EQual uu___1 -> x
     | FStarC_Custard_Syntax.EAny -> x
     | FStarC_Custard_Syntax.EAbort uu___1 -> x
     | FStarC_Custard_Syntax.ECast (e1, t) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = go env FStar_Pervasives_Native.None e1 in
             (uu___3, t) in
           FStarC_Custard_Syntax.ECast uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.ECoerce (e1, t) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = go env FStar_Pervasives_Native.None e1 in
             (uu___3, t) in
           FStarC_Custard_Syntax.ECoerce uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.EOp (o, es) when
         match o.FStarC_Custard_Syntax.po_op with
         | FStarC_Custard_Syntax.Eq -> true
         | FStarC_Custard_Syntax.Neq -> true
         | FStarC_Custard_Syntax.Lt -> true
         | FStarC_Custard_Syntax.Lte -> true
         | FStarC_Custard_Syntax.Gt -> true
         | FStarC_Custard_Syntax.Gte -> true
         | uu___1 -> false ->
         let es1 = FStarC_List.map (go env FStar_Pervasives_Native.None) es in
         let ts = FStarC_List.map (infer env) es1 in
         let known =
           FStarC_List.tryFind
             (fun t ->
                match t with
                | FStar_Pervasives_Native.Some c ->
                    Prims.not
                      (match c with
                       | FStarC_Custard_Syntax.TAny -> true
                       | uu___1 -> false)
                | FStar_Pervasives_Native.None -> false) ts in
         (match known with
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some c) ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_List.map2
                      (fun t e ->
                         match t with
                         | FStar_Pervasives_Native.Some
                             (FStarC_Custard_Syntax.TAny) -> coerce e c
                         | uu___4 -> e) ts es1 in
                  (o, uu___3) in
                FStarC_Custard_Syntax.EOp uu___2 in
              same uu___1
          | uu___1 -> same (FStarC_Custard_Syntax.EOp (o, es1)))
     | FStarC_Custard_Syntax.EOp (o, es) ->
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStarC_List.map (go env FStar_Pervasives_Native.None) es in
             (o, uu___3) in
           FStarC_Custard_Syntax.EOp uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.EWhile (c, b) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = check env cond_ty c in
             let uu___4 = go env FStar_Pervasives_Native.None b in
             (uu___3, uu___4) in
           FStarC_Custard_Syntax.EWhile uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.ERaise e1 ->
         let uu___1 =
           let uu___2 =
             check env
               (FStar_Pervasives_Native.Some FStarC_Custard_Syntax.TExn) e1 in
           FStarC_Custard_Syntax.ERaise uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.ESeq (a, b) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = go env FStar_Pervasives_Native.None a in
             let uu___4 = check env exp b in (uu___3, uu___4) in
           FStarC_Custard_Syntax.ESeq uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.ELet (v, t, e1, e2) ->
         let e11 = let uu___1 = trust t in check env uu___1 e1 in
         let b = binding env t e11 in
         let t1 =
           match b with
           | FStar_Pervasives_Native.Some bt when
               let uu___1 = has_any t in
               if uu___1
               then let uu___2 = has_any bt in Prims.not uu___2
               else false -> bt
           | uu___1 -> t in
         let uu___1 =
           let uu___2 =
             let uu___3 = let uu___4 = extend env v b in check uu___4 exp e2 in
             (v, t1, e11, uu___3) in
           FStarC_Custard_Syntax.ELet uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.EIf (c, a, b) ->
         let exp1 =
           let uu___1 =
             let uu___2 = infer env a in
             let uu___3 = infer env b in first uu___2 uu___3 in
           first exp uu___1 in
         let uu___1 =
           let uu___2 =
             let uu___3 = check env cond_ty c in
             let uu___4 = check env exp1 a in
             let uu___5 = check env exp1 b in (uu___3, uu___4, uu___5) in
           FStarC_Custard_Syntax.EIf uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.ETuple es ->
         let ts =
           match exp with
           | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TTuple ts1)
               when (FStarC_List.length ts1) = (FStarC_List.length es) ->
               FStarC_List.map
                 (fun uu___1 -> FStar_Pervasives_Native.Some uu___1) ts1
           | uu___1 ->
               FStarC_List.map (fun uu___2 -> FStar_Pervasives_Native.None)
                 es in
         let uu___1 =
           let uu___2 = FStarC_List.map2 (check env) ts es in
           FStarC_Custard_Syntax.ETuple uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.EFun (bs, body) ->
         let hint b =
           if
             match b.FStarC_Custard_Syntax.b_ty with
             | FStarC_Custard_Syntax.TAny -> true
             | uu___1 -> false
           then FStar_Pervasives_Native.Some FStarC_Custard_Syntax.TAny
           else trust b.FStarC_Custard_Syntax.b_ty in
         let uu___1 =
           match exp with
           | FStar_Pervasives_Native.Some t ->
               (match peel_arrows (FStarC_List.length bs) t with
                | FStar_Pervasives_Native.Some (ps, res) ->
                    let uu___2 =
                      FStarC_List.map
                        (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
                        ps in
                    (uu___2, (FStar_Pervasives_Native.Some res))
                | FStar_Pervasives_Native.None ->
                    let uu___2 = FStarC_List.map hint bs in
                    (uu___2, FStar_Pervasives_Native.None))
           | FStar_Pervasives_Native.None ->
               let uu___2 = FStarC_List.map hint bs in
               (uu___2, FStar_Pervasives_Native.None) in
         (match uu___1 with
          | (ps, res) ->
              let env1 =
                FStarC_List.fold_left
                  (fun env2 uu___2 ->
                     match uu___2 with
                     | (b, t) -> extend env2 b.FStarC_Custard_Syntax.b_name t)
                  env (FStarC_List.zip bs ps) in
              let uu___2 =
                let uu___3 = let uu___4 = check env1 res body in (bs, uu___4) in
                FStarC_Custard_Syntax.EFun uu___3 in
              same uu___2)
     | FStarC_Custard_Syntax.EApp (h, es) ->
         let uu___1 = infer env h in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t ->
              (match peel_arrows (FStarC_List.length es) t with
               | FStar_Pervasives_Native.Some (ps, uu___2) ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = go env FStar_Pervasives_Native.None h in
                       let uu___6 =
                         FStarC_List.map2
                           (fun p e ->
                              check env (FStar_Pervasives_Native.Some p) e)
                           ps es in
                       (uu___5, uu___6) in
                     FStarC_Custard_Syntax.EApp uu___4 in
                   same uu___3
               | FStar_Pervasives_Native.None ->
                   let es1 =
                     FStarC_List.map (go env FStar_Pervasives_Native.None) es in
                   let ts = FStarC_List.map (infer env) es1 in
                   let want =
                     match exp with
                     | FStar_Pervasives_Native.Some r when
                         FStarC_List.for_all
                           FStar_Pervasives_Native.uu___is_Some ts
                         ->
                         let uu___2 =
                           let uu___3 =
                             FStarC_List.map
                               (fun t1 ->
                                  match t1 with
                                  | FStar_Pervasives_Native.Some t2 -> t2
                                  | FStar_Pervasives_Native.None ->
                                      FStarC_Custard_Syntax.TAny) ts in
                           arrows uu___3 r in
                         FStar_Pervasives_Native.Some uu___2
                     | uu___2 -> FStar_Pervasives_Native.None in
                   (match want with
                    | FStar_Pervasives_Native.Some uu___2 ->
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = check env want h in (uu___5, es1) in
                          FStarC_Custard_Syntax.EApp uu___4 in
                        same uu___3
                    | FStar_Pervasives_Native.None ->
                        let h1 = go env FStar_Pervasives_Native.None h in
                        let uu___2 = infer env h1 in
                        (match uu___2 with
                         | FStar_Pervasives_Native.Some
                             (FStarC_Custard_Syntax.TAny) ->
                             same
                               (FStarC_Custard_Syntax.EApp
                                  ((coerce h1 FStarC_Custard_Syntax.TAny),
                                    es1))
                         | FStar_Pervasives_Native.Some t1 when
                             over_applied (FStarC_List.length es1) t1 ->
                             same
                               (FStarC_Custard_Syntax.EApp
                                  ((coerce h1 FStarC_Custard_Syntax.TAny),
                                    es1))
                         | uu___3 ->
                             same (FStarC_Custard_Syntax.EApp (h1, es1)))))
          | FStar_Pervasives_Native.None ->
              let ps =
                match peel_arrows (FStarC_List.length es)
                        h.FStarC_Custard_Syntax.ty
                with
                | FStar_Pervasives_Native.Some (ps1, uu___2) ->
                    FStarC_List.map
                      (fun p ->
                         if
                           match p with
                           | FStarC_Custard_Syntax.TAny -> true
                           | uu___3 -> false
                         then
                           FStar_Pervasives_Native.Some
                             FStarC_Custard_Syntax.TAny
                         else
                           (let uu___3 = has_any p in
                            if uu___3
                            then FStar_Pervasives_Native.None
                            else FStar_Pervasives_Native.Some p)) ps1
                | FStar_Pervasives_Native.None ->
                    FStarC_List.map
                      (fun uu___2 -> FStar_Pervasives_Native.None) es in
              let uu___2 =
                let uu___3 =
                  let uu___4 = go env FStar_Pervasives_Native.None h in
                  let uu___5 =
                    FStarC_List.map2 (fun p e -> check env p e) ps es in
                  (uu___4, uu___5) in
                FStarC_Custard_Syntax.EApp uu___3 in
              same uu___2)
     | FStarC_Custard_Syntax.ECtor (n, es) ->
         let fs =
           let uu___1 = FStarC_Custard_Syntax.string_of_name n in
           let uu___2 =
             let uu___3 = trust x.FStarC_Custard_Syntax.ty in
             first exp uu___3 in
           fields_of1 uu___1 uu___2 in
         if (FStarC_List.length fs) = (FStarC_List.length es)
         then
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 FStarC_List.map2
                   (fun uu___4 e ->
                      match uu___4 with
                      | (uu___5, t) ->
                          check env (FStar_Pervasives_Native.Some t) e) fs es in
               (n, uu___3) in
             FStarC_Custard_Syntax.ECtor uu___2 in
           same uu___1
         else
           (let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_List.map (go env FStar_Pervasives_Native.None) es in
                (n, uu___3) in
              FStarC_Custard_Syntax.ECtor uu___2 in
            same uu___1)
     | FStarC_Custard_Syntax.ERecord (n, fs) ->
         let owner =
           let uu___1 = trust x.FStarC_Custard_Syntax.ty in first exp uu___1 in
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStarC_List.map
                 (fun uu___4 ->
                    match uu___4 with
                    | (f, e) ->
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStarC_Custard_Syntax.string_of_name n in
                            field_of uu___7 owner f in
                          check env uu___6 e in
                        (f, uu___5)) fs in
             (n, uu___3) in
           FStarC_Custard_Syntax.ERecord uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.EProj (e1, n, f) ->
         let e11 = go env FStar_Pervasives_Native.None e1 in
         let uu___1 =
           let uu___2 = infer env e11 in
           let uu___3 =
             let uu___4 = FStarC_Custard_Syntax.string_of_name n in
             owner_of uu___4 in
           (uu___2, uu___3) in
         (match uu___1 with
          | (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TAny),
             FStar_Pervasives_Native.Some t) ->
              same (FStarC_Custard_Syntax.EProj ((coerce e11 t), n, f))
          | uu___2 -> same (FStarC_Custard_Syntax.EProj (e11, n, f)))
     | FStarC_Custard_Syntax.EDiscrim (e1, n) ->
         let e11 = go env FStar_Pervasives_Native.None e1 in
         let uu___1 =
           let uu___2 = infer env e11 in
           let uu___3 =
             let uu___4 = FStarC_Custard_Syntax.string_of_name n in
             owner_of uu___4 in
           (uu___2, uu___3) in
         (match uu___1 with
          | (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TAny),
             FStar_Pervasives_Native.Some t) ->
              same (FStarC_Custard_Syntax.EDiscrim ((coerce e11 t), n))
          | uu___2 -> same (FStarC_Custard_Syntax.EDiscrim (e11, n)))
     | FStarC_Custard_Syntax.EMatch (sc, brs) ->
         let sc1 = go env FStar_Pervasives_Native.None sc in
         let sc2 =
           let uu___1 =
             let uu___2 = infer env sc1 in
             let uu___3 = scrutinee_of brs in (uu___2, uu___3) in
           match uu___1 with
           | (FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.TAny),
              FStar_Pervasives_Native.Some t) -> coerce sc1 t
           | uu___2 -> sc1 in
         let st = infer env sc2 in
         let exp1 = let uu___1 = branches_ty env brs in first exp uu___1 in
         let uu___1 =
           let uu___2 =
             let uu___3 = FStarC_List.map (check_branch env st exp1) brs in
             (sc2, uu___3) in
           FStarC_Custard_Syntax.EMatch uu___2 in
         same uu___1
     | FStarC_Custard_Syntax.ETry (e1, brs) ->
         let exp1 =
           let uu___1 =
             let uu___2 = infer env e1 in
             let uu___3 = branches_ty env brs in first uu___2 uu___3 in
           first exp uu___1 in
         let uu___1 =
           let uu___2 =
             let uu___3 = check env exp1 e1 in
             let uu___4 =
               FStarC_List.map
                 (check_branch env FStar_Pervasives_Native.None exp1) brs in
             (uu___3, uu___4) in
           FStarC_Custard_Syntax.ETry uu___2 in
         same uu___1
   and check_branch env sc exp br =
     let uu___1 = br in
     match uu___1 with
     | (p, g, b) ->
         let env1 = bind_pat env sc p in
         let uu___2 =
           match g with
           | FStar_Pervasives_Native.Some g1 ->
               let uu___3 = go env1 FStar_Pervasives_Native.None g1 in
               FStar_Pervasives_Native.Some uu___3
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
         let uu___3 = check env1 exp b in (p, uu___2, uu___3)
   and branches_ty env brs =
     match brs with
     | [] -> FStar_Pervasives_Native.None
     | (p, uu___1, b)::brs1 ->
         let uu___2 =
           let uu___3 = bind_pat env FStar_Pervasives_Native.None p in
           infer uu___3 b in
         let uu___3 = branches_ty env brs1 in first uu___2 uu___3 in
   FStarC_List.map
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl ->
            let env = FStarC_SMap.create (Prims.of_int 20) in
            (FStarC_List.iter
               (fun b ->
                  FStarC_SMap.add env b.FStarC_Custard_Syntax.b_name
                    (FStar_Pervasives_Native.Some
                       (b.FStarC_Custard_Syntax.b_ty)))
               dl.FStarC_Custard_Syntax.dl_binders;
             (let uu___2 =
                let uu___3 =
                  check env
                    (FStar_Pervasives_Native.Some
                       (dl.FStarC_Custard_Syntax.dl_ret))
                    dl.FStarC_Custard_Syntax.dl_body in
                {
                  FStarC_Custard_Syntax.dl_name =
                    (dl.FStarC_Custard_Syntax.dl_name);
                  FStarC_Custard_Syntax.dl_typars =
                    (dl.FStarC_Custard_Syntax.dl_typars);
                  FStarC_Custard_Syntax.dl_binders =
                    (dl.FStarC_Custard_Syntax.dl_binders);
                  FStarC_Custard_Syntax.dl_ret =
                    (dl.FStarC_Custard_Syntax.dl_ret);
                  FStarC_Custard_Syntax.dl_eff =
                    (dl.FStarC_Custard_Syntax.dl_eff);
                  FStarC_Custard_Syntax.dl_body = uu___3;
                  FStarC_Custard_Syntax.dl_flags =
                    (dl.FStarC_Custard_Syntax.dl_flags)
                } in
              FStarC_Custard_Syntax.DLet uu___2))
        | d1 -> d1) prog)
let lift_lambdas (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let rec fvs bound x =
    let l es = FStarC_List.collect (fvs bound) es in
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EVar v ->
        if FStarC_List.mem v bound then [] else [v]
    | FStarC_Custard_Syntax.ELet (v, uu___, e1, e2) ->
        let uu___1 = fvs bound e1 in
        let uu___2 = fvs (v :: bound) e2 in FStarC_List.op_At uu___1 uu___2
    | FStarC_Custard_Syntax.EFun (bs, b) ->
        let uu___ =
          let uu___1 =
            FStarC_List.map (fun b1 -> b1.FStarC_Custard_Syntax.b_name) bs in
          FStarC_List.op_At uu___1 bound in
        fvs uu___ b
    | FStarC_Custard_Syntax.EMatch (sc, brs) ->
        let uu___ = fvs bound sc in
        let uu___1 = FStarC_List.collect (fvs_branch bound) brs in
        FStarC_List.op_At uu___ uu___1
    | FStarC_Custard_Syntax.ETry (a, brs) ->
        let uu___ = fvs bound a in
        let uu___1 = FStarC_List.collect (fvs_branch bound) brs in
        FStarC_List.op_At uu___ uu___1
    | uu___ -> let uu___1 = FStarC_Custard_Syntax.children x in l uu___1
  and fvs_branch bound br =
    let uu___ = br in
    match uu___ with
    | (p, g, b) ->
        let bound1 =
          let uu___1 = pat_vars p in FStarC_List.op_At uu___1 bound in
        let uu___1 =
          match g with
          | FStar_Pervasives_Native.Some g1 -> fvs bound1 g1
          | FStar_Pervasives_Native.None -> [] in
        let uu___2 = fvs bound1 b in FStarC_List.op_At uu___1 uu___2
  and pat_vars p =
    match p with
    | FStarC_Custard_Syntax.PWild -> []
    | FStarC_Custard_Syntax.PConst uu___ -> []
    | FStarC_Custard_Syntax.PVar v -> [v]
    | FStarC_Custard_Syntax.PCtor (uu___, ps) ->
        FStarC_List.collect pat_vars ps
    | FStarC_Custard_Syntax.PTuple ps -> FStarC_List.collect pat_vars ps
    | FStarC_Custard_Syntax.POr ps -> FStarC_List.collect pat_vars ps
    | FStarC_Custard_Syntax.PRecord (uu___, fs) ->
        let uu___1 = FStarC_List.map FStar_Pervasives_Native.snd fs in
        FStarC_List.collect pat_vars uu___1 in
  let taken = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet d1 ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               d1.FStarC_Custard_Syntax.dl_name in
           FStarC_SMap.add taken uu___1 true
       | FStarC_Custard_Syntax.DType d1 ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               d1.FStarC_Custard_Syntax.dt_name in
           FStarC_SMap.add taken uu___1 true
       | FStarC_Custard_Syntax.DExternal d1 ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               d1.FStarC_Custard_Syntax.dx_name in
           FStarC_SMap.add taken uu___1 true
       | FStarC_Custard_Syntax.DExn d1 ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               d1.FStarC_Custard_Syntax.de_name in
           FStarC_SMap.add taken uu___1 true) prog;
  (let lifted = FStarC_Effect.mk_ref [] in
   let go_decl dl =
     let n = FStarC_Effect.mk_ref Prims.int_zero in
     let fresh_name uu___1 =
       let pick i =
         let uu___2 =
           let uu___3 =
             if i = Prims.int_zero
             then ""
             else
               (let uu___4 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                Prims.strcat "_" uu___4) in
           Prims.strcat "__lam" uu___3 in
         Prims.strcat
           (dl.FStarC_Custard_Syntax.dl_name).FStarC_Custard_Syntax.id uu___2 in
       let rec first i =
         let cand =
           let uu___2 = dl.FStarC_Custard_Syntax.dl_name in
           let uu___3 = pick i in
           {
             FStarC_Custard_Syntax.ns = (uu___2.FStarC_Custard_Syntax.ns);
             FStarC_Custard_Syntax.id = uu___3;
             FStarC_Custard_Syntax.spec = (uu___2.FStarC_Custard_Syntax.spec)
           } in
         let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Custard_Syntax.string_of_name cand in
             FStarC_SMap.try_find taken uu___4 in
           match uu___3 with
           | FStar_Pervasives_Native.Some v -> true
           | uu___4 -> false in
         if uu___2
         then first (i + Prims.int_one)
         else
           ((let uu___4 = FStarC_Custard_Syntax.string_of_name cand in
             FStarC_SMap.add taken uu___4 true);
            cand) in
       let r = let uu___2 = FStarC_Effect.op_Bang n in first uu___2 in
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang n in uu___4 + Prims.int_one in
        FStarC_Effect.op_Colon_Equals n uu___3);
       r in
     let rec go x =
       let same e' =
         {
           FStarC_Custard_Syntax.e = e';
           FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
           FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
         } in
       match x.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EFun (bs, body) ->
           let body1 = go body in
           let bound =
             FStarC_List.map (fun b -> b.FStarC_Custard_Syntax.b_name) bs in
           let uu___1 =
             let uu___2 = fvs bound body1 in
             match uu___2 with | hd::tl -> true | uu___3 -> false in
           if uu___1
           then same (FStarC_Custard_Syntax.EFun (bs, body1))
           else
             (let nm = fresh_name () in
              (let uu___3 =
                 let uu___4 = FStarC_Effect.op_Bang lifted in
                 (FStarC_Custard_Syntax.DLet
                    {
                      FStarC_Custard_Syntax.dl_name = nm;
                      FStarC_Custard_Syntax.dl_typars =
                        (dl.FStarC_Custard_Syntax.dl_typars);
                      FStarC_Custard_Syntax.dl_binders = bs;
                      FStarC_Custard_Syntax.dl_ret =
                        (body1.FStarC_Custard_Syntax.ty);
                      FStarC_Custard_Syntax.dl_eff =
                        (body1.FStarC_Custard_Syntax.eff);
                      FStarC_Custard_Syntax.dl_body = body1;
                      FStarC_Custard_Syntax.dl_flags = []
                    })
                   :: uu___4 in
               FStarC_Effect.op_Colon_Equals lifted uu___3);
              (let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     FStarC_List.map (fun v -> FStarC_Custard_Syntax.TVar v)
                       dl.FStarC_Custard_Syntax.dl_typars in
                   (nm, uu___5) in
                 FStarC_Custard_Syntax.EQual uu___4 in
               {
                 FStarC_Custard_Syntax.e = uu___3;
                 FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
                 FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
               }))
       | uu___1 -> FStarC_Custard_Syntax.map_children go x in
     let uu___1 = go dl.FStarC_Custard_Syntax.dl_body in
     {
       FStarC_Custard_Syntax.dl_name = (dl.FStarC_Custard_Syntax.dl_name);
       FStarC_Custard_Syntax.dl_typars = (dl.FStarC_Custard_Syntax.dl_typars);
       FStarC_Custard_Syntax.dl_binders =
         (dl.FStarC_Custard_Syntax.dl_binders);
       FStarC_Custard_Syntax.dl_ret = (dl.FStarC_Custard_Syntax.dl_ret);
       FStarC_Custard_Syntax.dl_eff = (dl.FStarC_Custard_Syntax.dl_eff);
       FStarC_Custard_Syntax.dl_body = uu___1;
       FStarC_Custard_Syntax.dl_flags = (dl.FStarC_Custard_Syntax.dl_flags)
     } in
   FStarC_List.collect
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl ->
            (FStarC_Effect.op_Colon_Equals lifted [];
             (let dl1 = go_decl dl in
              let uu___2 =
                let uu___3 = FStarC_Effect.op_Bang lifted in
                FStarC_List.rev uu___3 in
              FStarC_List.op_At uu___2 [FStarC_Custard_Syntax.DLet dl1]))
        | d1 -> [d1]) prog)
let narrow_rets (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let rec has_any c =
    match c with
    | FStarC_Custard_Syntax.TAny -> true
    | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
        let uu___1 = has_any a in if uu___1 then true else has_any b
    | FStarC_Custard_Syntax.TApp (uu___, args) ->
        FStarC_List.existsb has_any args
    | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.existsb has_any cs
    | FStarC_Custard_Syntax.TBuf c1 -> has_any c1
    | FStarC_Custard_Syntax.TRef c1 -> has_any c1
    | FStarC_Custard_Syntax.TInline c1 -> has_any c1
    | FStarC_Custard_Syntax.TVar uu___ -> false
    | FStarC_Custard_Syntax.TInt uu___ -> false
    | FStarC_Custard_Syntax.TFloat uu___ -> false
    | FStarC_Custard_Syntax.TUnit -> false
    | FStarC_Custard_Syntax.TExn -> false
    | FStarC_Custard_Syntax.TConst uu___ -> false in
  let tbl = FStarC_SMap.create (Prims.of_int 100) in
  let full dl r =
    let uu___ =
      FStarC_List.map (fun b -> b.FStarC_Custard_Syntax.b_ty)
        dl.FStarC_Custard_Syntax.dl_binders in
    arrows uu___ r in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl when
           match dl.FStarC_Custard_Syntax.dl_typars with
           | [] -> true
           | uu___1 -> false ->
           let uu___1 =
             FStarC_Custard_Syntax.string_of_name
               dl.FStarC_Custard_Syntax.dl_name in
           let uu___2 = full dl dl.FStarC_Custard_Syntax.dl_ret in
           FStarC_SMap.add tbl uu___1 uu___2
       | uu___1 -> ()) prog;
  (let rec body_ty x =
     match x.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.ECoerce (e1, FStarC_Custard_Syntax.TAny) ->
         body_ty e1
     | FStarC_Custard_Syntax.EQual (n, []) ->
         let uu___1 =
           let uu___2 = FStarC_Custard_Syntax.string_of_name n in
           FStarC_SMap.try_find tbl uu___2 in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t when
              let uu___2 = has_any t in Prims.not uu___2 -> t
          | uu___2 -> x.FStarC_Custard_Syntax.ty)
     | FStarC_Custard_Syntax.EApp
         ({ FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EQual (n, []);
            FStarC_Custard_Syntax.ty = uu___1;
            FStarC_Custard_Syntax.eff = uu___2;_},
          es)
         ->
         let uu___3 =
           let uu___4 = FStarC_Custard_Syntax.string_of_name n in
           FStarC_SMap.try_find tbl uu___4 in
         (match uu___3 with
          | FStar_Pervasives_Native.Some t ->
              (match peel_arrows (FStarC_List.length es) t with
               | FStar_Pervasives_Native.Some (uu___4, res) when
                   let uu___5 = has_any res in Prims.not uu___5 -> res
               | uu___4 -> x.FStarC_Custard_Syntax.ty)
          | FStar_Pervasives_Native.None -> x.FStarC_Custard_Syntax.ty)
     | uu___1 -> x.FStarC_Custard_Syntax.ty in
   let changed = FStarC_Effect.mk_ref false in
   let round uu___1 =
     FStarC_List.iter
       (fun d ->
          match d with
          | FStarC_Custard_Syntax.DLet dl when
              if
                match dl.FStarC_Custard_Syntax.dl_typars with
                | [] -> true
                | uu___2 -> false
              then has_any dl.FStarC_Custard_Syntax.dl_ret
              else false ->
              let key =
                FStarC_Custard_Syntax.string_of_name
                  dl.FStarC_Custard_Syntax.dl_name in
              let cur =
                let uu___2 = FStarC_SMap.try_find tbl key in
                match uu___2 with
                | FStar_Pervasives_Native.Some t ->
                    (match peel_arrows
                             (FStarC_List.length
                                dl.FStarC_Custard_Syntax.dl_binders) t
                     with
                     | FStar_Pervasives_Native.Some (uu___3, r) -> r
                     | FStar_Pervasives_Native.None ->
                         dl.FStarC_Custard_Syntax.dl_ret)
                | FStar_Pervasives_Native.None ->
                    dl.FStarC_Custard_Syntax.dl_ret in
              let uu___2 = has_any cur in
              if uu___2
              then
                let r = body_ty dl.FStarC_Custard_Syntax.dl_body in
                let uu___3 = let uu___4 = has_any r in Prims.not uu___4 in
                (if uu___3
                 then
                   ((let uu___5 = full dl r in FStarC_SMap.add tbl key uu___5);
                    FStarC_Effect.op_Colon_Equals changed true)
                 else ())
              else ()
          | uu___2 -> ()) prog in
   let rec loop n =
     if n <= Prims.int_zero
     then ()
     else
       (FStarC_Effect.op_Colon_Equals changed false;
        round ();
        (let uu___3 = FStarC_Effect.op_Bang changed in
         if uu___3 then loop (n - Prims.int_one) else ())) in
   loop (Prims.of_int 20);
   FStarC_List.map
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl when
            if
              match dl.FStarC_Custard_Syntax.dl_typars with
              | [] -> true
              | uu___2 -> false
            then has_any dl.FStarC_Custard_Syntax.dl_ret
            else false ->
            let uu___2 =
              let uu___3 =
                FStarC_Custard_Syntax.string_of_name
                  dl.FStarC_Custard_Syntax.dl_name in
              FStarC_SMap.try_find tbl uu___3 in
            (match uu___2 with
             | FStar_Pervasives_Native.Some t ->
                 (match peel_arrows
                          (FStarC_List.length
                             dl.FStarC_Custard_Syntax.dl_binders) t
                  with
                  | FStar_Pervasives_Native.Some (uu___3, r) when
                      let uu___4 = has_any r in Prims.not uu___4 ->
                      FStarC_Custard_Syntax.DLet
                        {
                          FStarC_Custard_Syntax.dl_name =
                            (dl.FStarC_Custard_Syntax.dl_name);
                          FStarC_Custard_Syntax.dl_typars =
                            (dl.FStarC_Custard_Syntax.dl_typars);
                          FStarC_Custard_Syntax.dl_binders =
                            (dl.FStarC_Custard_Syntax.dl_binders);
                          FStarC_Custard_Syntax.dl_ret = r;
                          FStarC_Custard_Syntax.dl_eff =
                            (dl.FStarC_Custard_Syntax.dl_eff);
                          FStarC_Custard_Syntax.dl_body =
                            (dl.FStarC_Custard_Syntax.dl_body);
                          FStarC_Custard_Syntax.dl_flags =
                            (dl.FStarC_Custard_Syntax.dl_flags)
                        }
                  | uu___3 -> d)
             | FStar_Pervasives_Native.None -> d)
        | d1 -> d1) prog)
let rec const_shape (x : FStarC_Custard_Syntax.expr) : Prims.bool=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst uu___ -> true
  | FStarC_Custard_Syntax.ECast (e1, uu___) -> const_shape e1
  | FStarC_Custard_Syntax.ECoerce (e1, uu___) -> const_shape e1
  | FStarC_Custard_Syntax.EOp (o, es) ->
      (match o.FStarC_Custard_Syntax.po_op with
       | FStarC_Custard_Syntax.Add ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.AddW ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Sub ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.SubW ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Mult ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.MultW ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Div ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.DivW ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Mod ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.BOr ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.BAnd ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.BXor ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.BShiftL ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.BShiftR ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.BNot ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Eq ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Neq ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Lt ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Lte ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Gt ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Gte ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.And ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Or ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | FStarC_Custard_Syntax.Not ->
           (match o.FStarC_Custard_Syntax.po_ty with
            | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
                uu___) -> false
            | uu___ -> FStarC_List.for_all const_shape es)
       | uu___ -> false)
  | uu___ -> false
let const_globals (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let tbl = FStarC_SMap.create (Prims.of_int 50) in
  let rec subst1 x =
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EQual (n, []) ->
        let uu___ =
          let uu___1 = FStarC_Custard_Syntax.string_of_name n in
          FStarC_SMap.try_find tbl uu___1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some e -> e
         | FStar_Pervasives_Native.None -> x)
    | FStarC_Custard_Syntax.ECast (e1, c) ->
        let uu___ =
          let uu___1 = let uu___2 = subst1 e1 in (uu___2, c) in
          FStarC_Custard_Syntax.ECast uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | FStarC_Custard_Syntax.ECoerce (e1, c) ->
        let uu___ =
          let uu___1 = let uu___2 = subst1 e1 in (uu___2, c) in
          FStarC_Custard_Syntax.ECoerce uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | FStarC_Custard_Syntax.EOp (o, es) ->
        let uu___ =
          let uu___1 = let uu___2 = FStarC_List.map subst1 es in (o, uu___2) in
          FStarC_Custard_Syntax.EOp uu___1 in
        {
          FStarC_Custard_Syntax.e = uu___;
          FStarC_Custard_Syntax.ty = (x.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
        }
    | uu___ -> x in
  FStarC_List.map
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet dl when
           let uu___ =
             if
               (match dl.FStarC_Custard_Syntax.dl_binders with
                | [] -> true
                | uu___1 -> false) &&
                 (match dl.FStarC_Custard_Syntax.dl_typars with
                  | [] -> true
                  | uu___1 -> false)
             then
               let uu___1 = FStarC_Custard_Syntax.imported_unit d in
               match uu___1 with
               | FStar_Pervasives_Native.None -> true
               | uu___2 -> false
             else false in
           if uu___
           then
             let uu___1 =
               FStarC_List.existsb FStarC_Custard_Syntax.uu___is_CMacro
                 dl.FStarC_Custard_Syntax.dl_flags in
             Prims.not uu___1
           else false ->
           let body = subst1 dl.FStarC_Custard_Syntax.dl_body in
           let uu___ = const_shape body in
           if uu___
           then
             ((let uu___2 =
                 FStarC_Custard_Syntax.string_of_name
                   dl.FStarC_Custard_Syntax.dl_name in
               FStarC_SMap.add tbl uu___2 body);
              FStarC_Custard_Syntax.DLet
                {
                  FStarC_Custard_Syntax.dl_name =
                    (dl.FStarC_Custard_Syntax.dl_name);
                  FStarC_Custard_Syntax.dl_typars =
                    (dl.FStarC_Custard_Syntax.dl_typars);
                  FStarC_Custard_Syntax.dl_binders =
                    (dl.FStarC_Custard_Syntax.dl_binders);
                  FStarC_Custard_Syntax.dl_ret =
                    (dl.FStarC_Custard_Syntax.dl_ret);
                  FStarC_Custard_Syntax.dl_eff =
                    (dl.FStarC_Custard_Syntax.dl_eff);
                  FStarC_Custard_Syntax.dl_body = body;
                  FStarC_Custard_Syntax.dl_flags =
                    (dl.FStarC_Custard_Syntax.dl_flags)
                })
           else
             FStarC_Custard_Syntax.DLet
               {
                 FStarC_Custard_Syntax.dl_name =
                   (dl.FStarC_Custard_Syntax.dl_name);
                 FStarC_Custard_Syntax.dl_typars =
                   (dl.FStarC_Custard_Syntax.dl_typars);
                 FStarC_Custard_Syntax.dl_binders =
                   (dl.FStarC_Custard_Syntax.dl_binders);
                 FStarC_Custard_Syntax.dl_ret =
                   (dl.FStarC_Custard_Syntax.dl_ret);
                 FStarC_Custard_Syntax.dl_eff =
                   (dl.FStarC_Custard_Syntax.dl_eff);
                 FStarC_Custard_Syntax.dl_body = body;
                 FStarC_Custard_Syntax.dl_flags =
                   (dl.FStarC_Custard_Syntax.dl_flags)
               }
       | d1 -> d1) prog
let run (imports : FStarC_Custard_Syntax.decl Prims.list)
  (vd : FStarC_Custard_Syntax.verdicts)
  (prog : FStarC_Custard_Syntax.program) : FStarC_Custard_Syntax.program=
  let pass n f p =
    FStarC_Custard_Prof.timed (Prims.strcat "s." n) (fun uu___ -> f p) in
  FStarC_Effect.op_Colon_Equals imported_types imports;
  (let uu___2 = with_imports prog in record_ctor_tables uu___2);
  (let prog1 = pass "eta_ctors" (eta_ctors vd) prog in
   let prog2 = pass "eta_reduce" eta_reduce_decls prog1 in
   let prog3 = pass "inline" inline_decls prog2 in
   let prog4 =
     pass "reduce"
       (fun prog5 ->
          (let uu___3 = forwarder_table prog5 in
           FStarC_Effect.op_Colon_Equals forwarders uu___3);
          reduce_decls prog5) prog3 in
   let prog5 = pass "prune" prune_decls prog4 in
   let prog6 = pass "depat" depat_decls prog5 in
   let prog7 = pass "inline_fields" (inline_fields vd) prog6 in
   let prog8 = pass "unbuild" unbuild_decls prog7 in
   let simpl_all prog9 =
     FStarC_List.map
       (fun d ->
          match d with
          | FStarC_Custard_Syntax.DLet dl ->
              let uu___2 =
                let uu___3 = simpl dl.FStarC_Custard_Syntax.dl_body in
                {
                  FStarC_Custard_Syntax.dl_name =
                    (dl.FStarC_Custard_Syntax.dl_name);
                  FStarC_Custard_Syntax.dl_typars =
                    (dl.FStarC_Custard_Syntax.dl_typars);
                  FStarC_Custard_Syntax.dl_binders =
                    (dl.FStarC_Custard_Syntax.dl_binders);
                  FStarC_Custard_Syntax.dl_ret =
                    (dl.FStarC_Custard_Syntax.dl_ret);
                  FStarC_Custard_Syntax.dl_eff =
                    (dl.FStarC_Custard_Syntax.dl_eff);
                  FStarC_Custard_Syntax.dl_body = uu___3;
                  FStarC_Custard_Syntax.dl_flags =
                    (dl.FStarC_Custard_Syntax.dl_flags)
                } in
              FStarC_Custard_Syntax.DLet uu___2
          | d1 -> d1) prog9 in
   let prog9 = pass "simpl" simpl_all prog8 in
   let prog10 =
     let uu___2 =
       FStarC_List.existsb
         (fun d ->
            match d with
            | FStarC_Custard_Syntax.DLet dl -> is_identity dl
            | uu___3 -> false) prog9 in
     if uu___2
     then
       let prog11 = pass "inline_ids" inline_decls prog9 in
       pass "simpl_ids" simpl_all prog11
     else prog9 in
   let prog11 = pass "eta_expand" eta_expand_decls prog10 in
   let prog12 = pass "eta_rename" eta_rename_decls prog11 in
   let prog13 =
     let uu___2 =
       let uu___3 = FStarC_Options.custard_backend () in uu___3 = "C" in
     if uu___2 then pass "lift_lambdas" lift_lambdas prog12 else prog12 in
   let prog14 = pass "const_globals" const_globals prog13 in
   let prog15 = pass "dce" dce prog14 in
   let prog16 = pass "check_resolved" check_resolved prog15 in
   let prog17 = pass "propagate_prologues" propagate_prologues prog16 in
   let prog18 = pass "scc" scc prog17 in
   let prog19 = pass "records" (records vd) prog18 in
   let prog20 = pass "narrow_rets" narrow_rets prog19 in
   let prog21 = pass "split_any" split_any_decls prog20 in
   let prog22 = pass "coerce" coerce_prog prog21 in
   let uu___2 =
     let uu___3 = FStarC_Options.custard_backend () in
     FStarC_List.mem uu___3 ["KrmlC"; "KrmlRust"] in
   if uu___2 then pass "unit_args" unit_args prog22 else prog22)
