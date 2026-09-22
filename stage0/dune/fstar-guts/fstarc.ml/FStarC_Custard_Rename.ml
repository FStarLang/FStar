open Prims
type scope =
  {
  sub: (Prims.string * Prims.string) Prims.list ;
  used: Prims.string Prims.list }
let __proj__Mkscope__item__sub (projectee : scope) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | { sub; used;_} -> sub
let __proj__Mkscope__item__used (projectee : scope) :
  Prims.string Prims.list= match projectee with | { sub; used;_} -> used
let empty_scope : scope= { sub = []; used = [] }
let preferred (x : Prims.string) : Prims.string=
  let b = FStarC_Custard_Syntax.base_name x in
  let b1 =
    let uu___ =
      if (FStarC_String.length b) >= (Prims.of_int 4)
      then
        let uu___1 =
          FStarC_String.substring b Prims.int_zero (Prims.of_int 4) in
        uu___1 = "uu__"
      else false in
    if uu___ then "tmp" else b in
  if b1 = "" then "x" else b1
let taken (s : scope) (x : Prims.string) : Prims.bool=
  FStarC_List.existsb (fun u -> u = x) s.used
let rec pick (s : scope) (b : Prims.string) (i : Prims.int) : Prims.string=
  let cand =
    if i = Prims.int_zero
    then b
    else
      (let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
       Prims.strcat b uu___) in
  let uu___ = taken s cand in
  if uu___ then pick s b (i + Prims.int_one) else cand
let bind (s : scope) (x : Prims.string) : (Prims.string * scope)=
  let n = let uu___ = preferred x in pick s uu___ Prims.int_zero in
  (n, { sub = ((x, n) :: (s.sub)); used = (n :: (s.used)) })
let lookup (s : scope) (x : Prims.string) : Prims.string=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (a, uu___2) -> a = x) s.sub in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, n) -> n
  | FStar_Pervasives_Native.None -> preferred x
let rec bind_all (s : scope) (xs : Prims.string Prims.list) :
  (Prims.string Prims.list * scope)=
  match xs with
  | [] -> ([], s)
  | x::xs1 ->
      let uu___ = bind s x in
      (match uu___ with
       | (n, s1) ->
           let uu___1 = bind_all s1 xs1 in
           (match uu___1 with | (ns, s2) -> ((n :: ns), s2)))
let rec rn_cty (ts : scope) (c : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.cty=
  match c with
  | FStarC_Custard_Syntax.TVar x ->
      let uu___ = lookup ts x in FStarC_Custard_Syntax.TVar uu___
  | FStarC_Custard_Syntax.TArrow (a, e, b) ->
      let uu___ =
        let uu___1 = rn_cty ts a in
        let uu___2 = rn_cty ts b in (uu___1, e, uu___2) in
      FStarC_Custard_Syntax.TArrow uu___
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ =
        let uu___1 = FStarC_List.map (rn_cty ts) args in (n, uu___1) in
      FStarC_Custard_Syntax.TApp uu___
  | FStarC_Custard_Syntax.TBuf t ->
      let uu___ = rn_cty ts t in FStarC_Custard_Syntax.TBuf uu___
  | FStarC_Custard_Syntax.TRef t ->
      let uu___ = rn_cty ts t in FStarC_Custard_Syntax.TRef uu___
  | FStarC_Custard_Syntax.TInline t ->
      let uu___ = rn_cty ts t in FStarC_Custard_Syntax.TInline uu___
  | FStarC_Custard_Syntax.TTuple cs ->
      let uu___ = FStarC_List.map (rn_cty ts) cs in
      FStarC_Custard_Syntax.TTuple uu___
  | c1 -> c1
let field_key (n : FStarC_Custard_Syntax.name) (f : Prims.string) :
  Prims.string=
  let uu___ = FStarC_Custard_Syntax.string_of_name n in
  Prims.strcat uu___ (Prims.strcat "." f)
let rn_field (fields : Prims.string FStarC_SMap.t)
  (n : FStarC_Custard_Syntax.name) (f : Prims.string) : Prims.string=
  let uu___ =
    let uu___1 = field_key n f in FStarC_SMap.try_find fields uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some f' -> f'
  | FStar_Pervasives_Native.None -> preferred f
let rec rn_pat (fields : Prims.string FStarC_SMap.t) (s : scope)
  (p : FStarC_Custard_Syntax.pat) : (FStarC_Custard_Syntax.pat * scope)=
  match p with
  | FStarC_Custard_Syntax.PWild -> (p, s)
  | FStarC_Custard_Syntax.PConst uu___ -> (p, s)
  | FStarC_Custard_Syntax.PVar x ->
      let uu___ = bind s x in
      (match uu___ with | (n, s1) -> ((FStarC_Custard_Syntax.PVar n), s1))
  | FStarC_Custard_Syntax.PCtor (n, ps) ->
      let uu___ = rn_pats fields s ps in
      (match uu___ with
       | (ps1, s1) -> ((FStarC_Custard_Syntax.PCtor (n, ps1)), s1))
  | FStarC_Custard_Syntax.PRecord (n, fs) ->
      let uu___ =
        FStarC_List.fold_left
          (fun uu___1 uu___2 ->
             match (uu___1, uu___2) with
             | ((acc, s1), (f, q)) ->
                 let uu___3 = rn_pat fields s1 q in
                 (match uu___3 with
                  | (q1, s2) ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = rn_field fields n f in (uu___7, q1) in
                          [uu___6] in
                        FStarC_List.op_At acc uu___5 in
                      (uu___4, s2))) ([], s) fs in
      (match uu___ with
       | (fs1, s1) -> ((FStarC_Custard_Syntax.PRecord (n, fs1)), s1))
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = rn_pats fields s ps in
      (match uu___ with
       | (ps1, s1) -> ((FStarC_Custard_Syntax.PTuple ps1), s1))
  | FStarC_Custard_Syntax.POr ps ->
      let uu___ = rn_pats fields s ps in
      (match uu___ with | (ps1, s1) -> ((FStarC_Custard_Syntax.POr ps1), s1))
and rn_pats (fields : Prims.string FStarC_SMap.t) (s : scope)
  (ps : FStarC_Custard_Syntax.pat Prims.list) :
  (FStarC_Custard_Syntax.pat Prims.list * scope)=
  match ps with
  | [] -> ([], s)
  | p::ps1 ->
      let uu___ = rn_pat fields s p in
      (match uu___ with
       | (p1, s1) ->
           let uu___1 = rn_pats fields s1 ps1 in
           (match uu___1 with | (ps2, s2) -> ((p1 :: ps2), s2)))
let rec rn_expr (fields : Prims.string FStarC_SMap.t) (ts : scope)
  (s : scope) (x : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  let go = rn_expr fields ts s in
  let ty = rn_cty ts x.FStarC_Custard_Syntax.ty in
  let e =
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EConst uu___ -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EAny -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EAbort uu___ -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EVar v ->
        let uu___ = lookup s v in FStarC_Custard_Syntax.EVar uu___
    | FStarC_Custard_Syntax.EQual (n, args) ->
        let uu___ =
          let uu___1 = FStarC_List.map (rn_cty ts) args in (n, uu___1) in
        FStarC_Custard_Syntax.EQual uu___
    | FStarC_Custard_Syntax.ELet (v, t, e1, e2) ->
        let t1 = rn_cty ts t in
        let e11 = go e1 in
        let uu___ = bind s v in
        (match uu___ with
         | (v', s') ->
             let uu___1 =
               let uu___2 = rn_expr fields ts s' e2 in (v', t1, e11, uu___2) in
             FStarC_Custard_Syntax.ELet uu___1)
    | FStarC_Custard_Syntax.EFun (bs, body) ->
        let uu___ = rn_binders ts s bs in
        (match uu___ with
         | (bs1, s') ->
             let uu___1 =
               let uu___2 = rn_expr fields ts s' body in (bs1, uu___2) in
             FStarC_Custard_Syntax.EFun uu___1)
    | FStarC_Custard_Syntax.EApp (h, args) ->
        let uu___ =
          let uu___1 = go h in
          let uu___2 = FStarC_List.map go args in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EApp uu___
    | FStarC_Custard_Syntax.EMatch (scrut, brs) ->
        let uu___ =
          let uu___1 = go scrut in
          let uu___2 = FStarC_List.map (rn_branch fields ts s) brs in
          (uu___1, uu___2) in
        FStarC_Custard_Syntax.EMatch uu___
    | FStarC_Custard_Syntax.EIf (c, t1, t2) ->
        let uu___ =
          let uu___1 = go c in
          let uu___2 = go t1 in
          let uu___3 = go t2 in (uu___1, uu___2, uu___3) in
        FStarC_Custard_Syntax.EIf uu___
    | FStarC_Custard_Syntax.ESeq (e1, e2) ->
        let uu___ =
          let uu___1 = go e1 in let uu___2 = go e2 in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ESeq uu___
    | FStarC_Custard_Syntax.ECtor (n, es) ->
        let uu___ = let uu___1 = FStarC_List.map go es in (n, uu___1) in
        FStarC_Custard_Syntax.ECtor uu___
    | FStarC_Custard_Syntax.ETuple es ->
        let uu___ = FStarC_List.map go es in
        FStarC_Custard_Syntax.ETuple uu___
    | FStarC_Custard_Syntax.ERecord (n, fs) ->
        let uu___ =
          let uu___1 =
            FStarC_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (f, e1) ->
                     let uu___3 = rn_field fields n f in
                     let uu___4 = go e1 in (uu___3, uu___4)) fs in
          (n, uu___1) in
        FStarC_Custard_Syntax.ERecord uu___
    | FStarC_Custard_Syntax.EProj (e1, n, f) ->
        let uu___ =
          let uu___1 = go e1 in
          let uu___2 = rn_field fields n f in (uu___1, n, uu___2) in
        FStarC_Custard_Syntax.EProj uu___
    | FStarC_Custard_Syntax.EDiscrim (e1, n) ->
        let uu___ = let uu___1 = go e1 in (uu___1, n) in
        FStarC_Custard_Syntax.EDiscrim uu___
    | FStarC_Custard_Syntax.ECast (e1, t) ->
        let uu___ =
          let uu___1 = go e1 in let uu___2 = rn_cty ts t in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ECast uu___
    | FStarC_Custard_Syntax.ECoerce (e1, t) ->
        let uu___ =
          let uu___1 = go e1 in let uu___2 = rn_cty ts t in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ECoerce uu___
    | FStarC_Custard_Syntax.EOp (o, es) ->
        let uu___ = let uu___1 = FStarC_List.map go es in (o, uu___1) in
        FStarC_Custard_Syntax.EOp uu___
    | FStarC_Custard_Syntax.EWhile (c, b) ->
        let uu___ =
          let uu___1 = go c in let uu___2 = go b in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EWhile uu___
    | FStarC_Custard_Syntax.ERaise e1 ->
        let uu___ = go e1 in FStarC_Custard_Syntax.ERaise uu___
    | FStarC_Custard_Syntax.ETry (e1, brs) ->
        let uu___ =
          let uu___1 = go e1 in
          let uu___2 = FStarC_List.map (rn_branch fields ts s) brs in
          (uu___1, uu___2) in
        FStarC_Custard_Syntax.ETry uu___ in
  {
    FStarC_Custard_Syntax.e = e;
    FStarC_Custard_Syntax.ty = ty;
    FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
  }
and rn_branch (fields : Prims.string FStarC_SMap.t) (ts : scope) (s : scope)
  (br : FStarC_Custard_Syntax.branch) : FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 = rn_pat fields s p in
      (match uu___1 with
       | (p1, s1) ->
           let uu___2 =
             match g with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some g1 ->
                 let uu___3 = rn_expr fields ts s1 g1 in
                 FStar_Pervasives_Native.Some uu___3 in
           let uu___3 = rn_expr fields ts s1 b in (p1, uu___2, uu___3))
and rn_binders (ts : scope) (s : scope)
  (bs : FStarC_Custard_Syntax.binder Prims.list) :
  (FStarC_Custard_Syntax.binder Prims.list * scope)=
  match bs with
  | [] -> ([], s)
  | b::bs1 ->
      let t = rn_cty ts b.FStarC_Custard_Syntax.b_ty in
      let uu___ = bind s b.FStarC_Custard_Syntax.b_name in
      (match uu___ with
       | (n, s1) ->
           let uu___1 = rn_binders ts s1 bs1 in
           (match uu___1 with
            | (bs2, s2) ->
                (({
                    FStarC_Custard_Syntax.b_name = n;
                    FStarC_Custard_Syntax.b_ty = t
                  } :: bs2), s2)))
let rn_fields (fields : Prims.string FStarC_SMap.t)
  (n : FStarC_Custard_Syntax.name) (ts : scope)
  (fs : (Prims.string * FStarC_Custard_Syntax.cty) Prims.list) :
  (Prims.string * FStarC_Custard_Syntax.cty) Prims.list=
  let rec go s fs1 =
    match fs1 with
    | [] -> []
    | (f, c)::fs2 ->
        let uu___ = bind s f in
        (match uu___ with
         | (f', s1) ->
             ((let uu___2 = field_key n f in FStarC_SMap.add fields uu___2 f');
              (let uu___2 = let uu___3 = rn_cty ts c in (f', uu___3) in
               let uu___3 = go s1 fs2 in uu___2 :: uu___3))) in
  go empty_scope fs
let rn_tydef (fields : Prims.string FStarC_SMap.t)
  (self : FStarC_Custard_Syntax.name) (ts : scope)
  (b : FStarC_Custard_Syntax.tydef) : FStarC_Custard_Syntax.tydef=
  match b with
  | FStarC_Custard_Syntax.TAbbrev c ->
      let uu___ = rn_cty ts c in FStarC_Custard_Syntax.TAbbrev uu___
  | FStarC_Custard_Syntax.TRecord fs ->
      let uu___ = rn_fields fields self ts fs in
      FStarC_Custard_Syntax.TRecord uu___
  | FStarC_Custard_Syntax.TVariant cs ->
      let uu___ =
        FStarC_List.map
          (fun uu___1 ->
             match uu___1 with
             | (cn, fs) ->
                 let uu___2 = rn_fields fields cn ts fs in (cn, uu___2)) cs in
      FStarC_Custard_Syntax.TVariant uu___
  | FStarC_Custard_Syntax.TAbstract -> FStarC_Custard_Syntax.TAbstract
let rn_types (fields : Prims.string FStarC_SMap.t)
  (d : FStarC_Custard_Syntax.decl) : FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      let uu___ = bind_all empty_scope t.FStarC_Custard_Syntax.dt_params in
      (match uu___ with
       | (params, ts) ->
           let uu___1 =
             let uu___2 =
               rn_tydef fields t.FStarC_Custard_Syntax.dt_name ts
                 t.FStarC_Custard_Syntax.dt_body in
             {
               FStarC_Custard_Syntax.dt_name =
                 (t.FStarC_Custard_Syntax.dt_name);
               FStarC_Custard_Syntax.dt_params = params;
               FStarC_Custard_Syntax.dt_body = uu___2;
               FStarC_Custard_Syntax.dt_flags =
                 (t.FStarC_Custard_Syntax.dt_flags)
             } in
           FStarC_Custard_Syntax.DType uu___1)
  | d1 -> d1
let rn_terms (fields : Prims.string FStarC_SMap.t)
  (d : FStarC_Custard_Syntax.decl) : FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType uu___ -> d
  | FStarC_Custard_Syntax.DLet l ->
      let uu___ = bind_all empty_scope l.FStarC_Custard_Syntax.dl_typars in
      (match uu___ with
       | (typars, ts) ->
           let uu___1 =
             rn_binders ts empty_scope l.FStarC_Custard_Syntax.dl_binders in
           (match uu___1 with
            | (binders, s) ->
                let uu___2 =
                  let uu___3 = rn_cty ts l.FStarC_Custard_Syntax.dl_ret in
                  let uu___4 =
                    rn_expr fields ts s l.FStarC_Custard_Syntax.dl_body in
                  {
                    FStarC_Custard_Syntax.dl_name =
                      (l.FStarC_Custard_Syntax.dl_name);
                    FStarC_Custard_Syntax.dl_typars = typars;
                    FStarC_Custard_Syntax.dl_binders = binders;
                    FStarC_Custard_Syntax.dl_ret = uu___3;
                    FStarC_Custard_Syntax.dl_eff =
                      (l.FStarC_Custard_Syntax.dl_eff);
                    FStarC_Custard_Syntax.dl_body = uu___4;
                    FStarC_Custard_Syntax.dl_flags =
                      (l.FStarC_Custard_Syntax.dl_flags)
                  } in
                FStarC_Custard_Syntax.DLet uu___2))
  | FStarC_Custard_Syntax.DExternal x ->
      let uu___ = bind_all empty_scope x.FStarC_Custard_Syntax.dx_typars in
      (match uu___ with
       | (typars, ts) ->
           let uu___1 =
             let uu___2 = rn_cty ts x.FStarC_Custard_Syntax.dx_ty in
             {
               FStarC_Custard_Syntax.dx_name =
                 (x.FStarC_Custard_Syntax.dx_name);
               FStarC_Custard_Syntax.dx_typars = typars;
               FStarC_Custard_Syntax.dx_ty = uu___2;
               FStarC_Custard_Syntax.dx_target =
                 (x.FStarC_Custard_Syntax.dx_target);
               FStarC_Custard_Syntax.dx_header =
                 (x.FStarC_Custard_Syntax.dx_header);
               FStarC_Custard_Syntax.dx_flags =
                 (x.FStarC_Custard_Syntax.dx_flags)
             } in
           FStarC_Custard_Syntax.DExternal uu___1)
  | FStarC_Custard_Syntax.DExn e ->
      let uu___ =
        let uu___1 =
          FStarC_List.map (rn_cty empty_scope)
            e.FStarC_Custard_Syntax.de_args in
        {
          FStarC_Custard_Syntax.de_name = (e.FStarC_Custard_Syntax.de_name);
          FStarC_Custard_Syntax.de_args = uu___1;
          FStarC_Custard_Syntax.de_flags = (e.FStarC_Custard_Syntax.de_flags)
        } in
      FStarC_Custard_Syntax.DExn uu___
let rn_type_info (fields : Prims.string FStarC_SMap.t)
  (ti : FStarC_Custard_Syntax.type_info) : FStarC_Custard_Syntax.type_info=
  let rn_cl cl =
    let uu___ =
      FStarC_List.map
        (fun uu___1 ->
           match uu___1 with
           | (f, c) ->
               let uu___2 =
                 rn_field fields cl.FStarC_Custard_Syntax.cl_name f in
               (uu___2, c)) cl.FStarC_Custard_Syntax.cl_fields in
    {
      FStarC_Custard_Syntax.cl_name = (cl.FStarC_Custard_Syntax.cl_name);
      FStarC_Custard_Syntax.cl_tag = (cl.FStarC_Custard_Syntax.cl_tag);
      FStarC_Custard_Syntax.cl_slots = (cl.FStarC_Custard_Syntax.cl_slots);
      FStarC_Custard_Syntax.cl_arity = (cl.FStarC_Custard_Syntax.cl_arity);
      FStarC_Custard_Syntax.cl_fields = uu___
    } in
  let uu___ =
    match ti.FStarC_Custard_Syntax.ti_layout with
    | FStarC_Custard_Syntax.L_newtype nt ->
        let uu___1 =
          let uu___2 =
            rn_field fields nt.FStarC_Custard_Syntax.nt_ctor
              nt.FStarC_Custard_Syntax.nt_field in
          {
            FStarC_Custard_Syntax.nt_ctor =
              (nt.FStarC_Custard_Syntax.nt_ctor);
            FStarC_Custard_Syntax.nt_field = uu___2;
            FStarC_Custard_Syntax.nt_index =
              (nt.FStarC_Custard_Syntax.nt_index);
            FStarC_Custard_Syntax.nt_ty = (nt.FStarC_Custard_Syntax.nt_ty)
          } in
        FStarC_Custard_Syntax.L_newtype uu___1
    | FStarC_Custard_Syntax.L_struct cls ->
        let uu___1 = FStarC_List.map rn_cl cls in
        FStarC_Custard_Syntax.L_struct uu___1
    | l -> l in
  let uu___1 = FStarC_List.map rn_cl ti.FStarC_Custard_Syntax.ti_ctors in
  {
    FStarC_Custard_Syntax.ti_erased = (ti.FStarC_Custard_Syntax.ti_erased);
    FStarC_Custard_Syntax.ti_layout = uu___;
    FStarC_Custard_Syntax.ti_ctors = uu___1;
    FStarC_Custard_Syntax.ti_record = (ti.FStarC_Custard_Syntax.ti_record);
    FStarC_Custard_Syntax.ti_plans = (ti.FStarC_Custard_Syntax.ti_plans)
  }
let run
  (infos :
    (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.type_info) Prims.list)
  (prog : FStarC_Custard_Syntax.program) :
  (FStarC_Custard_Syntax.program * (FStarC_Custard_Syntax.name *
    FStarC_Custard_Syntax.type_info) Prims.list)=
  let fields = FStarC_SMap.create (Prims.of_int 50) in
  let prog1 = FStarC_List.map (rn_types fields) prog in
  let prog2 = FStarC_List.map (rn_terms fields) prog1 in
  let uu___ =
    FStarC_List.map
      (fun uu___1 ->
         match uu___1 with
         | (n, ti) -> let uu___2 = rn_type_info fields ti in (n, uu___2))
      infos in
  (prog2, uu___)
