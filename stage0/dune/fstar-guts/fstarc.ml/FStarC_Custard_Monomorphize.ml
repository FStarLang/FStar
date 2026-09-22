open Prims
let key_of (n : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list) : Prims.string=
  let uu___ = FStarC_Custard_Syntax.string_of_name n in
  let uu___1 =
    let uu___2 =
      let uu___3 =
        let uu___4 =
          FStarC_List.map
            (FStarC_Class_Show.show FStarC_Custard_Syntax.showable_cty) args in
        FStarC_String.concat "," uu___4 in
      Prims.strcat uu___3 ">" in
    Prims.strcat "<" uu___2 in
  Prims.strcat uu___ uu___1
let hint_width : Prims.int= Prims.of_int 48
let hint_depth : Prims.int= Prims.of_int 4
let rec hint_of_cty (fuel : Prims.int) (c : FStarC_Custard_Syntax.cty) :
  Prims.string=
  if fuel <= Prims.int_zero
  then "x"
  else
    (let sub c1 = hint_of_cty (fuel - Prims.int_one) c1 in
     match c with
     | FStarC_Custard_Syntax.TVar v -> v
     | FStarC_Custard_Syntax.TInt (s, w) ->
         Prims.strcat
           (match s with
            | FStarC_Const.Signed -> "int"
            | FStarC_Const.Unsigned -> "uint")
           (match w with
            | FStarC_Custard_Syntax.W8 -> "8"
            | FStarC_Custard_Syntax.W16 -> "16"
            | FStarC_Custard_Syntax.W32 -> "32"
            | FStarC_Custard_Syntax.W64 -> "64"
            | FStarC_Custard_Syntax.W128 -> "128"
            | FStarC_Custard_Syntax.WSizet -> "size")
     | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float32) ->
         "float32"
     | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float64) ->
         "float64"
     | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float16) ->
         "float16"
     | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.BFloat16) ->
         "bfloat16"
     | FStarC_Custard_Syntax.TApp (n, []) ->
         (match n.FStarC_Custard_Syntax.spec with
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat n.FStarC_Custard_Syntax.id (Prims.strcat "_" s)
          | FStar_Pervasives_Native.None -> n.FStarC_Custard_Syntax.id)
     | FStarC_Custard_Syntax.TApp (n, args) ->
         let uu___ =
           let uu___1 =
             let uu___2 = FStarC_List.map sub args in
             FStarC_String.concat "_" uu___2 in
           Prims.strcat "_" uu___1 in
         Prims.strcat n.FStarC_Custard_Syntax.id uu___
     | FStarC_Custard_Syntax.TBuf c1 ->
         let uu___ = sub c1 in Prims.strcat uu___ "_ptr"
     | FStarC_Custard_Syntax.TRef c1 ->
         let uu___ = sub c1 in Prims.strcat uu___ "_ref"
     | FStarC_Custard_Syntax.TInline c1 -> hint_of_cty fuel c1
     | FStarC_Custard_Syntax.TTuple cs ->
         let uu___ =
           let uu___1 = FStarC_List.map sub cs in
           FStarC_String.concat "_" uu___1 in
         Prims.strcat "tup" uu___
     | FStarC_Custard_Syntax.TUnit -> "unit"
     | FStarC_Custard_Syntax.TExn -> "exn"
     | FStarC_Custard_Syntax.TArrow uu___ -> "fn"
     | FStarC_Custard_Syntax.TAny -> "any"
     | FStarC_Custard_Syntax.TConst (FStarC_Custard_Syntax.CInt
         (v, uu___, uu___1)) ->
         FStarC_Class_Show.show FStarC_Class_Show.showable_int v
     | FStarC_Custard_Syntax.TConst (FStarC_Custard_Syntax.CBool b) ->
         if b then "true" else "false"
     | FStarC_Custard_Syntax.TConst uu___ -> "const")
let clip (s : Prims.string) : Prims.string=
  if (FStarC_String.length s) <= hint_width
  then s
  else FStarC_String.substring s Prims.int_zero hint_width
type state =
  {
  types: FStarC_Custard_Syntax.dtype FStarC_SMap.t ;
  frozen: Prims.bool FStarC_SMap.t ;
  names: FStarC_Custard_Syntax.name FStarC_SMap.t ;
  taken: Prims.bool FStarC_SMap.t ;
  clones: FStarC_Custard_Syntax.dtype Prims.list FStarC_Effect.ref ;
  todo:
    (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.name *
      FStarC_Custard_Syntax.cty Prims.list) Prims.list FStarC_Effect.ref
    ;
  exts: FStarC_Custard_Syntax.dexternal FStarC_SMap.t ;
  ext_names: FStarC_Custard_Syntax.name FStarC_SMap.t ;
  ext_bare: Prims.bool FStarC_SMap.t ;
  ext_clones: FStarC_Custard_Syntax.dexternal Prims.list FStarC_Effect.ref }
let __proj__Mkstate__item__types (projectee : state) :
  FStarC_Custard_Syntax.dtype FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> types
let __proj__Mkstate__item__frozen (projectee : state) :
  Prims.bool FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> frozen
let __proj__Mkstate__item__names (projectee : state) :
  FStarC_Custard_Syntax.name FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> names
let __proj__Mkstate__item__taken (projectee : state) :
  Prims.bool FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> taken
let __proj__Mkstate__item__clones (projectee : state) :
  FStarC_Custard_Syntax.dtype Prims.list FStarC_Effect.ref=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> clones
let __proj__Mkstate__item__todo (projectee : state) :
  (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.name *
    FStarC_Custard_Syntax.cty Prims.list) Prims.list FStarC_Effect.ref=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> todo
let __proj__Mkstate__item__exts (projectee : state) :
  FStarC_Custard_Syntax.dexternal FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> exts
let __proj__Mkstate__item__ext_names (projectee : state) :
  FStarC_Custard_Syntax.name FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> ext_names
let __proj__Mkstate__item__ext_bare (projectee : state) :
  Prims.bool FStarC_SMap.t=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> ext_bare
let __proj__Mkstate__item__ext_clones (projectee : state) :
  FStarC_Custard_Syntax.dexternal Prims.list FStarC_Effect.ref=
  match projectee with
  | { types; frozen; names; taken; clones; todo; exts; ext_names; ext_bare;
      ext_clones;_} -> ext_clones
let freeze_realized (uu___ : unit) : Prims.bool=
  let uu___1 = FStarC_Options.custard_backend () in uu___1 = "OCaml"
let is_extern_type (st : state) (n : FStarC_Custard_Syntax.name) :
  Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find st.types uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some d ->
      FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Extern
        d.FStarC_Custard_Syntax.dt_flags
  | FStar_Pervasives_Native.None -> false
let is_template_type (st : state) (n : FStarC_Custard_Syntax.name) :
  Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find st.types uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some d ->
      let uu___1 =
        FStarC_Custard_Syntax.extern_template_of_flags
          d.FStarC_Custard_Syntax.dt_flags in
      (match uu___1 with
       | FStar_Pervasives_Native.Some v -> true
       | uu___2 -> false)
  | FStar_Pervasives_Native.None -> false
let is_poly (st : state) (n : FStarC_Custard_Syntax.name) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Custard_Syntax.string_of_name n in
      FStarC_SMap.try_find st.frozen uu___2 in
    match uu___1 with
    | FStar_Pervasives_Native.Some v -> true
    | uu___2 -> false in
  if uu___
  then false
  else
    (let uu___1 =
       let uu___2 = FStarC_Custard_Syntax.string_of_name n in
       FStarC_SMap.try_find st.types uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.Some d ->
         (match d.FStarC_Custard_Syntax.dt_params with
          | hd::tl -> true
          | uu___2 -> false)
     | FStar_Pervasives_Native.None -> false)
let is_poly_extern (st : state) (n : FStarC_Custard_Syntax.name) :
  Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find st.exts uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some d ->
      (match d.FStarC_Custard_Syntax.dx_typars with
       | hd::tl -> true
       | uu___1 -> false)
  | FStar_Pervasives_Native.None -> false
let with_spec (owner : FStarC_Custard_Syntax.name)
  (n : FStarC_Custard_Syntax.name) : FStarC_Custard_Syntax.name=
  {
    FStarC_Custard_Syntax.ns = (n.FStarC_Custard_Syntax.ns);
    FStarC_Custard_Syntax.id = (n.FStarC_Custard_Syntax.id);
    FStarC_Custard_Syntax.spec = (owner.FStarC_Custard_Syntax.spec)
  }
let rec zip_params (ps : Prims.string Prims.list)
  (args : FStarC_Custard_Syntax.cty Prims.list) :
  (Prims.string * FStarC_Custard_Syntax.cty) Prims.list=
  match (ps, args) with
  | (p::ps1, a::args1) -> (p, a) :: (zip_params ps1 args1)
  | uu___ -> []
let request (st : state) (n : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list) : FStarC_Custard_Syntax.name=
  let key = key_of n args in
  let uu___ = FStarC_SMap.try_find st.names key in
  match uu___ with
  | FStar_Pervasives_Native.Some nm -> nm
  | FStar_Pervasives_Native.None ->
      let hint =
        let uu___1 = FStarC_List.map (hint_of_cty hint_depth) args in
        FStarC_String.concat "_" uu___1 in
      let base =
        clip
          (Prims.strcat
             (match n.FStarC_Custard_Syntax.spec with
              | FStar_Pervasives_Native.Some s -> Prims.strcat s "_"
              | FStar_Pervasives_Native.None -> "") hint) in
      let rec pick i =
        let cand =
          if i = Prims.int_zero
          then base
          else
            (let uu___1 =
               let uu___2 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
               Prims.strcat "_" uu___2 in
             Prims.strcat base uu___1) in
        let k =
          let uu___1 =
            FStarC_Custard_Syntax.string_of_name
              {
                FStarC_Custard_Syntax.ns = (n.FStarC_Custard_Syntax.ns);
                FStarC_Custard_Syntax.id = (n.FStarC_Custard_Syntax.id);
                FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
              } in
          Prims.strcat uu___1 (Prims.strcat "__" cand) in
        let uu___1 =
          let uu___2 = FStarC_SMap.try_find st.taken k in
          match uu___2 with
          | FStar_Pervasives_Native.Some v -> true
          | uu___3 -> false in
        if uu___1
        then pick (i + Prims.int_one)
        else (FStarC_SMap.add st.taken k true; cand) in
      let nm =
        let uu___1 =
          let uu___2 = pick Prims.int_zero in
          FStar_Pervasives_Native.Some uu___2 in
        {
          FStarC_Custard_Syntax.ns = (n.FStarC_Custard_Syntax.ns);
          FStarC_Custard_Syntax.id = (n.FStarC_Custard_Syntax.id);
          FStarC_Custard_Syntax.spec = uu___1
        } in
      (FStarC_SMap.add st.names key nm;
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang st.todo in (n, nm, args) ::
            uu___4 in
        FStarC_Effect.op_Colon_Equals st.todo uu___3);
       nm)
let rec unfold_cty (st : state) (fuel : Prims.int)
  (c : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.cty=
  if fuel <= Prims.int_zero
  then c
  else
    (match c with
     | FStarC_Custard_Syntax.TApp (n, args) ->
         let uu___ =
           let uu___1 = FStarC_Custard_Syntax.string_of_name n in
           FStarC_SMap.try_find st.types uu___1 in
         (match uu___ with
          | FStar_Pervasives_Native.Some
              { FStarC_Custard_Syntax.dt_name = uu___1;
                FStarC_Custard_Syntax.dt_params = uu___2;
                FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TAbbrev
                  uu___3;
                FStarC_Custard_Syntax.dt_flags = fl;_}
              when
              FStarC_Custard_Syntax.has_flag fl
                FStarC_Custard_Syntax.Realized
              -> c
          | FStar_Pervasives_Native.Some
              { FStarC_Custard_Syntax.dt_name = uu___1;
                FStarC_Custard_Syntax.dt_params = ps;
                FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TAbbrev
                  b;
                FStarC_Custard_Syntax.dt_flags = uu___2;_}
              ->
              let np = FStarC_List.length ps in
              if (FStarC_List.length args) < np
              then c
              else
                (let uu___3 =
                   if (FStarC_List.length args) > np
                   then FStarC_List.splitAt np args
                   else (args, []) in
                 match uu___3 with
                 | (used, extra) ->
                     let b1 =
                       FStarC_Custard_Syntax.subst_cty (zip_params ps used) b in
                     let b2 =
                       match (extra, b1) with
                       | ([], uu___4) -> b1
                       | (uu___4, FStarC_Custard_Syntax.TApp (m, a)) ->
                           FStarC_Custard_Syntax.TApp
                             (m, (FStarC_List.op_At a extra))
                       | uu___4 -> b1 in
                     unfold_cty st (fuel - Prims.int_one) b2)
          | uu___1 -> c)
     | uu___ -> c)
let rec mono_cty (st : state) (c : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.cty=
  let c1 = unfold_cty st (Prims.of_int 100) c in
  match c1 with
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ = is_template_type st n in
      if uu___
      then
        let uu___1 =
          let uu___2 = FStarC_List.map (mono_cty st) args in (n, uu___2) in
        FStarC_Custard_Syntax.TApp uu___1
      else
        (let uu___1 = is_extern_type st n in
         if uu___1
         then FStarC_Custard_Syntax.TApp (n, [])
         else
           (let args1 = FStarC_List.map (mono_cty st) args in
            let uu___2 = is_poly st n in
            if uu___2
            then
              let uu___3 = let uu___4 = request st n args1 in (uu___4, []) in
              FStarC_Custard_Syntax.TApp uu___3
            else FStarC_Custard_Syntax.TApp (n, args1)))
  | FStarC_Custard_Syntax.TArrow (a, e, b) ->
      let uu___ =
        let uu___1 = mono_cty st a in
        let uu___2 = mono_cty st b in (uu___1, e, uu___2) in
      FStarC_Custard_Syntax.TArrow uu___
  | FStarC_Custard_Syntax.TBuf c2 ->
      let uu___ = mono_cty st c2 in FStarC_Custard_Syntax.TBuf uu___
  | FStarC_Custard_Syntax.TRef c2 ->
      let uu___ = mono_cty st c2 in FStarC_Custard_Syntax.TRef uu___
  | FStarC_Custard_Syntax.TInline c2 ->
      let uu___ = mono_cty st c2 in FStarC_Custard_Syntax.TInline uu___
  | FStarC_Custard_Syntax.TTuple cs ->
      let uu___ = FStarC_List.map (mono_cty st) cs in
      FStarC_Custard_Syntax.TTuple uu___
  | FStarC_Custard_Syntax.TVar uu___ -> c1
  | FStarC_Custard_Syntax.TInt uu___ -> c1
  | FStarC_Custard_Syntax.TFloat uu___ -> c1
  | FStarC_Custard_Syntax.TUnit -> c1
  | FStarC_Custard_Syntax.TExn -> c1
  | FStarC_Custard_Syntax.TAny -> c1
  | FStarC_Custard_Syntax.TConst uu___ -> c1
let resolve_owner (st : state) (t : FStarC_Custard_Syntax.cty) :
  (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.cty Prims.list)
    FStar_Pervasives_Native.option=
  let uu___ = unfold_cty st (Prims.of_int 100) t in
  match uu___ with
  | FStarC_Custard_Syntax.TApp (n, args) when is_poly st n ->
      FStar_Pervasives_Native.Some (n, args)
  | uu___1 -> FStar_Pervasives_Native.None
let shape_of (st : state) (t : FStarC_Custard_Syntax.cty) :
  (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.cty Prims.list)
    FStar_Pervasives_Native.option=
  let uu___ = unfold_cty st (Prims.of_int 100) t in
  match uu___ with
  | FStarC_Custard_Syntax.TApp (n, args) ->
      FStar_Pervasives_Native.Some (n, args)
  | uu___1 -> FStar_Pervasives_Native.None
let request_inst (st : state) (n : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list) : FStarC_Custard_Syntax.name=
  let uu___ = FStarC_List.map (mono_cty st) args in request st n uu___
let request_extern (st : state) (n : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list) : FStarC_Custard_Syntax.name=
  let key = key_of n args in
  let uu___ = FStarC_SMap.try_find st.ext_names key in
  match uu___ with
  | FStar_Pervasives_Native.Some nm -> nm
  | FStar_Pervasives_Native.None ->
      let hint =
        let uu___1 = FStarC_List.map (hint_of_cty hint_depth) args in
        FStarC_String.concat "_" uu___1 in
      let base =
        clip
          (Prims.strcat
             (match n.FStarC_Custard_Syntax.spec with
              | FStar_Pervasives_Native.Some s -> Prims.strcat s "_"
              | FStar_Pervasives_Native.None -> "") hint) in
      let rec pick i =
        let cand =
          if i = Prims.int_zero
          then base
          else
            (let uu___1 =
               let uu___2 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
               Prims.strcat "_" uu___2 in
             Prims.strcat base uu___1) in
        let k =
          let uu___1 =
            FStarC_Custard_Syntax.string_of_name
              {
                FStarC_Custard_Syntax.ns = (n.FStarC_Custard_Syntax.ns);
                FStarC_Custard_Syntax.id = (n.FStarC_Custard_Syntax.id);
                FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
              } in
          Prims.strcat uu___1 (Prims.strcat "__" cand) in
        let uu___1 =
          let uu___2 = FStarC_SMap.try_find st.taken k in
          match uu___2 with
          | FStar_Pervasives_Native.Some v -> true
          | uu___3 -> false in
        if uu___1
        then pick (i + Prims.int_one)
        else (FStarC_SMap.add st.taken k true; cand) in
      let nm =
        let uu___1 =
          let uu___2 = pick Prims.int_zero in
          FStar_Pervasives_Native.Some uu___2 in
        {
          FStarC_Custard_Syntax.ns = (n.FStarC_Custard_Syntax.ns);
          FStarC_Custard_Syntax.id = (n.FStarC_Custard_Syntax.id);
          FStarC_Custard_Syntax.spec = uu___1
        } in
      (FStarC_SMap.add st.ext_names key nm;
       (let uu___3 =
          let uu___4 = FStarC_Custard_Syntax.string_of_name n in
          FStarC_SMap.try_find st.exts uu___4 in
        match uu___3 with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some d ->
            let sub = zip_params d.FStarC_Custard_Syntax.dx_typars args in
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStarC_Custard_Syntax.subst_cty sub
                      d.FStarC_Custard_Syntax.dx_ty in
                  mono_cty st uu___7 in
                {
                  FStarC_Custard_Syntax.dx_name = nm;
                  FStarC_Custard_Syntax.dx_typars = [];
                  FStarC_Custard_Syntax.dx_ty = uu___6;
                  FStarC_Custard_Syntax.dx_target =
                    (d.FStarC_Custard_Syntax.dx_target);
                  FStarC_Custard_Syntax.dx_header =
                    (d.FStarC_Custard_Syntax.dx_header);
                  FStarC_Custard_Syntax.dx_flags =
                    (d.FStarC_Custard_Syntax.dx_flags)
                } in
              let uu___6 = FStarC_Effect.op_Bang st.ext_clones in uu___5 ::
                uu___6 in
            FStarC_Effect.op_Colon_Equals st.ext_clones uu___4);
       nm)
let ctor_fields (st : state) (owner : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list)
  (cn : FStarC_Custard_Syntax.name) : FStarC_Custard_Syntax.cty Prims.list=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.string_of_name owner in
    FStarC_SMap.try_find st.types uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some
      { FStarC_Custard_Syntax.dt_name = uu___1;
        FStarC_Custard_Syntax.dt_params = ps;
        FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TVariant cs;
        FStarC_Custard_Syntax.dt_flags = uu___2;_}
      ->
      let sub = zip_params ps args in
      let uu___3 =
        FStarC_List.tryFind
          (fun uu___4 ->
             match uu___4 with
             | (c, uu___5) ->
                 let uu___6 = FStarC_Custard_Syntax.string_of_name c in
                 let uu___7 = FStarC_Custard_Syntax.string_of_name cn in
                 uu___6 = uu___7) cs in
      (match uu___3 with
       | FStar_Pervasives_Native.Some (uu___4, fs) ->
           FStarC_List.map
             (fun uu___5 ->
                match uu___5 with
                | (uu___6, c) ->
                    FStarC_Custard_Syntax.subst_cty sub
                      (match c with
                       | FStarC_Custard_Syntax.TInline c1 -> c1
                       | c1 -> c1)) fs
       | FStar_Pervasives_Native.None -> [])
  | uu___1 -> []
let record_fields (st : state) (owner : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list) :
  (Prims.string * FStarC_Custard_Syntax.cty) Prims.list=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.string_of_name owner in
    FStarC_SMap.try_find st.types uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some
      { FStarC_Custard_Syntax.dt_name = uu___1;
        FStarC_Custard_Syntax.dt_params = ps;
        FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TRecord fs;
        FStarC_Custard_Syntax.dt_flags = uu___2;_}
      ->
      let sub = zip_params ps args in
      FStarC_List.map
        (fun uu___3 ->
           match uu___3 with
           | (f, c) ->
               let uu___4 =
                 FStarC_Custard_Syntax.subst_cty sub
                   (match c with
                    | FStarC_Custard_Syntax.TInline c1 -> c1
                    | c1 -> c1) in
               (f, uu___4)) fs
  | uu___1 -> []
type env = (Prims.string * FStarC_Custard_Syntax.cty) Prims.list
let lookup (env1 : env) (x : Prims.string) :
  FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___1 -> match uu___1 with | (y, uu___2) -> y = x) env1 in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, c) ->
      FStar_Pervasives_Native.Some c
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec mono_pat (st : state) (t : FStarC_Custard_Syntax.cty)
  (p : FStarC_Custard_Syntax.pat) : (FStarC_Custard_Syntax.pat * env)=
  let t1 = unfold_cty st (Prims.of_int 100) t in
  match p with
  | FStarC_Custard_Syntax.PCtor (cn, ps) ->
      let fields =
        let uu___ = shape_of st t1 in
        match uu___ with
        | FStar_Pervasives_Native.Some (n, args) -> ctor_fields st n args cn
        | FStar_Pervasives_Native.None -> [] in
      let cn' =
        let uu___ = resolve_owner st t1 in
        match uu___ with
        | FStar_Pervasives_Native.Some (owner, args) ->
            let uu___1 = request_inst st owner args in with_spec uu___1 cn
        | FStar_Pervasives_Native.None -> cn in
      let uu___ = mono_pats st fields ps in
      (match uu___ with
       | (ps', env1) -> ((FStarC_Custard_Syntax.PCtor (cn', ps')), env1))
  | FStarC_Custard_Syntax.PRecord (tn, fs) ->
      let fields =
        let uu___ = shape_of st t1 in
        match uu___ with
        | FStar_Pervasives_Native.Some (n, args) -> record_fields st n args
        | FStar_Pervasives_Native.None -> [] in
      let tn' =
        let uu___ = resolve_owner st t1 in
        match uu___ with
        | FStar_Pervasives_Native.Some (owner, args) ->
            request_inst st owner args
        | FStar_Pervasives_Native.None -> tn in
      let uu___ =
        FStarC_List.fold_left
          (fun uu___1 uu___2 ->
             match (uu___1, uu___2) with
             | ((acc, env1), (f, q)) ->
                 let ft =
                   let uu___3 =
                     FStarC_List.tryFind
                       (fun uu___4 ->
                          match uu___4 with | (g, uu___5) -> g = f) fields in
                   match uu___3 with
                   | FStar_Pervasives_Native.Some (uu___4, ft1) -> ft1
                   | FStar_Pervasives_Native.None ->
                       FStarC_Custard_Syntax.TAny in
                 let uu___3 = mono_pat st ft q in
                 (match uu___3 with
                  | (q', env') ->
                      ((FStarC_List.op_At acc [(f, q')]),
                        (FStarC_List.op_At env1 env')))) ([], []) fs in
      (match uu___ with
       | (fs', env1) -> ((FStarC_Custard_Syntax.PRecord (tn', fs')), env1))
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ =
        mono_pats st
          (match t1 with
           | FStarC_Custard_Syntax.TTuple cs -> cs
           | uu___1 -> []) ps in
      (match uu___ with
       | (ps', env1) -> ((FStarC_Custard_Syntax.PTuple ps'), env1))
  | FStarC_Custard_Syntax.POr ps ->
      let uu___ =
        let uu___1 = FStarC_List.map (mono_pat st t1) ps in
        FStarC_List.unzip uu___1 in
      (match uu___ with
       | (ps', envs) ->
           ((FStarC_Custard_Syntax.POr ps'),
             ((match envs with | e::uu___1 -> e | [] -> []))))
  | FStarC_Custard_Syntax.PVar x -> (p, [(x, t1)])
  | FStarC_Custard_Syntax.PWild -> (p, [])
  | FStarC_Custard_Syntax.PConst uu___ -> (p, [])
and mono_pats (st : state) (ts : FStarC_Custard_Syntax.cty Prims.list)
  (ps : FStarC_Custard_Syntax.pat Prims.list) :
  (FStarC_Custard_Syntax.pat Prims.list * env)=
  match (ts, ps) with
  | (t::ts1, p::ps1) ->
      let uu___ = mono_pat st t p in
      (match uu___ with
       | (p', e1) ->
           let uu___1 = mono_pats st ts1 ps1 in
           (match uu___1 with
            | (ps', e2) -> ((p' :: ps'), (FStarC_List.op_At e1 e2))))
  | ([], p::ps1) ->
      let uu___ = mono_pat st FStarC_Custard_Syntax.TAny p in
      (match uu___ with
       | (p', e1) ->
           let uu___1 = mono_pats st [] ps1 in
           (match uu___1 with
            | (ps', e2) -> ((p' :: ps'), (FStarC_List.op_At e1 e2))))
  | (uu___, []) -> ([], [])
let rec mono_expr (st : state) (env1 : env) (x : FStarC_Custard_Syntax.expr)
  : FStarC_Custard_Syntax.expr=
  let type_of e =
    match e.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EVar v ->
        let uu___ = lookup env1 v in
        (match uu___ with
         | FStar_Pervasives_Native.Some c -> c
         | FStar_Pervasives_Native.None -> e.FStarC_Custard_Syntax.ty)
    | uu___ -> e.FStarC_Custard_Syntax.ty in
  let owner_of t =
    let uu___ = resolve_owner st t in
    match uu___ with
    | FStar_Pervasives_Native.Some (o, args) ->
        let uu___1 = request_inst st o args in
        FStar_Pervasives_Native.Some uu___1
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let rename t cn =
    let uu___ = owner_of t in
    match uu___ with
    | FStar_Pervasives_Native.Some o -> with_spec o cn
    | FStar_Pervasives_Native.None -> cn in
  let go = mono_expr st env1 in
  let e' =
    match x.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EConst uu___ -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EVar uu___ -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EAny -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EAbort uu___ -> x.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EQual (n, args) ->
        let args1 = FStarC_List.map (mono_cty st) args in
        let uu___ = is_poly_extern st n in
        if uu___
        then
          (if match args1 with | hd::tl -> true | uu___1 -> false
           then
             let uu___1 =
               let uu___2 = request_extern st n args1 in (uu___2, []) in
             FStarC_Custard_Syntax.EQual uu___1
           else
             ((let uu___2 = FStarC_Custard_Syntax.string_of_name n in
               FStarC_SMap.add st.ext_bare uu___2 true);
              FStarC_Custard_Syntax.EQual (n, args1)))
        else FStarC_Custard_Syntax.EQual (n, args1)
    | FStarC_Custard_Syntax.ELet (v, t, e1, e2) ->
        let uu___ =
          let uu___1 = mono_cty st t in
          let uu___2 = go e1 in
          let uu___3 = mono_expr st ((v, t) :: env1) e2 in
          (v, uu___1, uu___2, uu___3) in
        FStarC_Custard_Syntax.ELet uu___
    | FStarC_Custard_Syntax.EApp (h, es) ->
        let uu___ =
          let uu___1 = go h in
          let uu___2 = FStarC_List.map go es in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EApp uu___
    | FStarC_Custard_Syntax.EFun (bs, b) ->
        let env2 =
          let uu___ =
            FStarC_List.map
              (fun b1 ->
                 ((b1.FStarC_Custard_Syntax.b_name),
                   (b1.FStarC_Custard_Syntax.b_ty))) bs in
          FStarC_List.op_At uu___ env1 in
        let uu___ =
          let uu___1 =
            FStarC_List.map
              (fun b1 ->
                 let uu___2 = mono_cty st b1.FStarC_Custard_Syntax.b_ty in
                 {
                   FStarC_Custard_Syntax.b_name =
                     (b1.FStarC_Custard_Syntax.b_name);
                   FStarC_Custard_Syntax.b_ty = uu___2
                 }) bs in
          let uu___2 = mono_expr st env2 b in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EFun uu___
    | FStarC_Custard_Syntax.EMatch (sc, brs) ->
        let t = type_of sc in
        let uu___ =
          let uu___1 = go sc in
          let uu___2 = FStarC_List.map (mono_branch st env1 t) brs in
          (uu___1, uu___2) in
        FStarC_Custard_Syntax.EMatch uu___
    | FStarC_Custard_Syntax.ETry (e, brs) ->
        let uu___ =
          let uu___1 = go e in
          let uu___2 =
            FStarC_List.map (mono_branch st env1 FStarC_Custard_Syntax.TAny)
              brs in
          (uu___1, uu___2) in
        FStarC_Custard_Syntax.ETry uu___
    | FStarC_Custard_Syntax.EIf (c, a, b) ->
        let uu___ =
          let uu___1 = go c in
          let uu___2 = go a in let uu___3 = go b in (uu___1, uu___2, uu___3) in
        FStarC_Custard_Syntax.EIf uu___
    | FStarC_Custard_Syntax.ESeq (a, b) ->
        let uu___ =
          let uu___1 = go a in let uu___2 = go b in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ESeq uu___
    | FStarC_Custard_Syntax.ECtor (cn, es) ->
        let uu___ =
          let uu___1 = rename x.FStarC_Custard_Syntax.ty cn in
          let uu___2 = FStarC_List.map go es in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ECtor uu___
    | FStarC_Custard_Syntax.ERaise e1 ->
        let uu___ = go e1 in FStarC_Custard_Syntax.ERaise uu___
    | FStarC_Custard_Syntax.ETuple es ->
        let uu___ = FStarC_List.map go es in
        FStarC_Custard_Syntax.ETuple uu___
    | FStarC_Custard_Syntax.ERecord (n, fs) ->
        let n' =
          let uu___ = owner_of x.FStarC_Custard_Syntax.ty in
          match uu___ with
          | FStar_Pervasives_Native.Some o -> o
          | FStar_Pervasives_Native.None -> n in
        let uu___ =
          let uu___1 =
            FStarC_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (f, e) -> let uu___3 = go e in (f, uu___3)) fs in
          (n', uu___1) in
        FStarC_Custard_Syntax.ERecord uu___
    | FStarC_Custard_Syntax.EProj (e, cn, f) ->
        let uu___ =
          let uu___1 = go e in
          let uu___2 = let uu___3 = type_of e in rename uu___3 cn in
          (uu___1, uu___2, f) in
        FStarC_Custard_Syntax.EProj uu___
    | FStarC_Custard_Syntax.EDiscrim (e, cn) ->
        let uu___ =
          let uu___1 = go e in
          let uu___2 = let uu___3 = type_of e in rename uu___3 cn in
          (uu___1, uu___2) in
        FStarC_Custard_Syntax.EDiscrim uu___
    | FStarC_Custard_Syntax.ECast (e, c) ->
        let uu___ =
          let uu___1 = go e in let uu___2 = mono_cty st c in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ECast uu___
    | FStarC_Custard_Syntax.ECoerce (e, c) ->
        let uu___ =
          let uu___1 = go e in let uu___2 = mono_cty st c in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ECoerce uu___
    | FStarC_Custard_Syntax.EOp (o, es) ->
        let uu___ = let uu___1 = FStarC_List.map go es in (o, uu___1) in
        FStarC_Custard_Syntax.EOp uu___
    | FStarC_Custard_Syntax.EWhile (c, b) ->
        let uu___ =
          let uu___1 = go c in let uu___2 = go b in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EWhile uu___ in
  let uu___ = mono_cty st x.FStarC_Custard_Syntax.ty in
  {
    FStarC_Custard_Syntax.e = e';
    FStarC_Custard_Syntax.ty = uu___;
    FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
  }
and mono_branch (st : state) (env1 : env) (t : FStarC_Custard_Syntax.cty)
  (br : FStarC_Custard_Syntax.branch) : FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 = mono_pat st t p in
      (match uu___1 with
       | (p', bound) ->
           let env2 = FStarC_List.op_At bound env1 in
           let uu___2 =
             match g with
             | FStar_Pervasives_Native.Some g1 ->
                 let uu___3 = mono_expr st env2 g1 in
                 FStar_Pervasives_Native.Some uu___3
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
           let uu___3 = mono_expr st env2 b in (p', uu___2, uu___3))
let rec drain (st : state) : unit=
  let uu___ = FStarC_Effect.op_Bang st.todo in
  match uu___ with
  | [] -> ()
  | (orig, nm, args)::rest ->
      (FStarC_Effect.op_Colon_Equals st.todo rest;
       (let uu___3 =
          let uu___4 = FStarC_Custard_Syntax.string_of_name orig in
          FStarC_SMap.try_find st.types uu___4 in
        match uu___3 with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some d ->
            let sub = zip_params d.FStarC_Custard_Syntax.dt_params args in
            let f c =
              let uu___4 = FStarC_Custard_Syntax.subst_cty sub c in
              mono_cty st uu___4 in
            let body =
              match d.FStarC_Custard_Syntax.dt_body with
              | FStarC_Custard_Syntax.TAbbrev c ->
                  let uu___4 = f c in FStarC_Custard_Syntax.TAbbrev uu___4
              | FStarC_Custard_Syntax.TRecord fs ->
                  let uu___4 =
                    FStarC_List.map
                      (fun uu___5 ->
                         match uu___5 with
                         | (x, c) -> let uu___6 = f c in (x, uu___6)) fs in
                  FStarC_Custard_Syntax.TRecord uu___4
              | FStarC_Custard_Syntax.TVariant cs ->
                  let uu___4 =
                    FStarC_List.map
                      (fun uu___5 ->
                         match uu___5 with
                         | (cn, fs) ->
                             let uu___6 =
                               FStarC_List.map
                                 (fun uu___7 ->
                                    match uu___7 with
                                    | (x, c) ->
                                        let uu___8 = f c in (x, uu___8)) fs in
                             ((with_spec nm cn), uu___6)) cs in
                  FStarC_Custard_Syntax.TVariant uu___4
              | FStarC_Custard_Syntax.TAbstract ->
                  FStarC_Custard_Syntax.TAbstract in
            let uu___4 =
              let uu___5 = FStarC_Effect.op_Bang st.clones in
              {
                FStarC_Custard_Syntax.dt_name = nm;
                FStarC_Custard_Syntax.dt_params = [];
                FStarC_Custard_Syntax.dt_body = body;
                FStarC_Custard_Syntax.dt_flags =
                  (d.FStarC_Custard_Syntax.dt_flags)
              } :: uu___5 in
            FStarC_Effect.op_Colon_Equals st.clones uu___4);
       drain st)
let run (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  let st =
    let uu___ = FStarC_SMap.create (Prims.of_int 100) in
    let uu___1 = FStarC_SMap.create (Prims.of_int 10) in
    let uu___2 = FStarC_SMap.create (Prims.of_int 100) in
    let uu___3 = FStarC_SMap.create (Prims.of_int 100) in
    let uu___4 = FStarC_Effect.mk_ref [] in
    let uu___5 = FStarC_Effect.mk_ref [] in
    let uu___6 = FStarC_SMap.create (Prims.of_int 20) in
    let uu___7 = FStarC_SMap.create (Prims.of_int 20) in
    let uu___8 = FStarC_SMap.create (Prims.of_int 20) in
    let uu___9 = FStarC_Effect.mk_ref [] in
    {
      types = uu___;
      frozen = uu___1;
      names = uu___2;
      taken = uu___3;
      clones = uu___4;
      todo = uu___5;
      exts = uu___6;
      ext_names = uu___7;
      ext_bare = uu___8;
      ext_clones = uu___9
    } in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t ->
           ((let uu___2 =
               FStarC_Custard_Syntax.string_of_name
                 t.FStarC_Custard_Syntax.dt_name in
             FStarC_SMap.add st.types uu___2 t);
            (let uu___2 =
               FStarC_Custard_Syntax.string_of_name
                 t.FStarC_Custard_Syntax.dt_name in
             FStarC_SMap.add st.taken uu___2 true))
       | FStarC_Custard_Syntax.DExternal x ->
           ((let uu___2 =
               FStarC_Custard_Syntax.string_of_name
                 x.FStarC_Custard_Syntax.dx_name in
             FStarC_SMap.add st.exts uu___2 x);
            (let uu___2 =
               FStarC_Custard_Syntax.string_of_name
                 x.FStarC_Custard_Syntax.dx_name in
             FStarC_SMap.add st.taken uu___2 true))
       | uu___1 -> ()) prog;
  (let rec freeze fuel c =
     if fuel <= Prims.int_zero
     then ()
     else
       (match c with
        | FStarC_Custard_Syntax.TApp (n, args) ->
            let k = FStarC_Custard_Syntax.string_of_name n in
            (FStarC_List.iter (freeze (fuel - Prims.int_one)) args;
             (let uu___2 =
                let uu___3 = FStarC_SMap.try_find st.frozen k in
                match uu___3 with
                | FStar_Pervasives_Native.None -> true
                | uu___4 -> false in
              if uu___2
              then
                (FStarC_SMap.add st.frozen k true;
                 (let uu___4 = FStarC_SMap.try_find st.types k in
                  match uu___4 with
                  | FStar_Pervasives_Native.Some d ->
                      (match d.FStarC_Custard_Syntax.dt_body with
                       | FStarC_Custard_Syntax.TAbbrev c1 ->
                           freeze (fuel - Prims.int_one) c1
                       | FStarC_Custard_Syntax.TRecord fs ->
                           FStarC_List.iter
                             (fun uu___5 ->
                                match uu___5 with
                                | (uu___6, c1) ->
                                    freeze (fuel - Prims.int_one) c1) fs
                       | FStarC_Custard_Syntax.TVariant cs ->
                           FStarC_List.iter
                             (fun uu___5 ->
                                match uu___5 with
                                | (uu___6, fs) ->
                                    FStarC_List.iter
                                      (fun uu___7 ->
                                         match uu___7 with
                                         | (uu___8, c1) ->
                                             freeze (fuel - Prims.int_one) c1)
                                      fs) cs
                       | FStarC_Custard_Syntax.TAbstract -> ())
                  | FStar_Pervasives_Native.None -> ()))
              else ()))
        | FStarC_Custard_Syntax.TArrow (a, uu___1, b) ->
            (freeze (fuel - Prims.int_one) a; freeze (fuel - Prims.int_one) b)
        | FStarC_Custard_Syntax.TBuf c1 -> freeze (fuel - Prims.int_one) c1
        | FStarC_Custard_Syntax.TRef c1 -> freeze (fuel - Prims.int_one) c1
        | FStarC_Custard_Syntax.TInline c1 ->
            freeze (fuel - Prims.int_one) c1
        | FStarC_Custard_Syntax.TTuple cs ->
            FStarC_List.iter (freeze (fuel - Prims.int_one)) cs
        | FStarC_Custard_Syntax.TVar uu___1 -> ()
        | FStarC_Custard_Syntax.TInt uu___1 -> ()
        | FStarC_Custard_Syntax.TFloat uu___1 -> ()
        | FStarC_Custard_Syntax.TUnit -> ()
        | FStarC_Custard_Syntax.TExn -> ()
        | FStarC_Custard_Syntax.TAny -> ()
        | FStarC_Custard_Syntax.TConst uu___1 -> ()) in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DExternal x when freeze_realized () ->
            freeze (Prims.of_int 100) x.FStarC_Custard_Syntax.dx_ty
        | FStarC_Custard_Syntax.DExn e ->
            FStarC_List.iter (freeze (Prims.of_int 100))
              e.FStarC_Custard_Syntax.de_args
        | FStarC_Custard_Syntax.DType t when
            FStarC_List.existsb
              (fun uu___2 ->
                 match uu___2 with
                 | FStarC_Custard_Syntax.Modelled -> true
                 | uu___3 -> false) t.FStarC_Custard_Syntax.dt_flags
            ->
            freeze (Prims.of_int 100)
              (FStarC_Custard_Syntax.TApp
                 ((t.FStarC_Custard_Syntax.dt_name), []))
        | FStarC_Custard_Syntax.DType t when
            let uu___2 = freeze_realized () in
            if uu___2
            then
              FStarC_List.existsb
                (fun uu___3 ->
                   match uu___3 with
                   | FStarC_Custard_Syntax.Realized -> true
                   | FStarC_Custard_Syntax.Imported uu___4 -> true
                   | uu___4 -> false) t.FStarC_Custard_Syntax.dt_flags
            else false ->
            freeze (Prims.of_int 100)
              (FStarC_Custard_Syntax.TApp
                 ((t.FStarC_Custard_Syntax.dt_name), []))
        | uu___2 -> ()) prog;
   (let rest =
      FStarC_List.collect
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DType t when
               is_extern_type st t.FStarC_Custard_Syntax.dt_name ->
               [FStarC_Custard_Syntax.DType
                  {
                    FStarC_Custard_Syntax.dt_name =
                      (t.FStarC_Custard_Syntax.dt_name);
                    FStarC_Custard_Syntax.dt_params = [];
                    FStarC_Custard_Syntax.dt_body =
                      (t.FStarC_Custard_Syntax.dt_body);
                    FStarC_Custard_Syntax.dt_flags =
                      (t.FStarC_Custard_Syntax.dt_flags)
                  }]
           | FStarC_Custard_Syntax.DType t when
               if
                 match t.FStarC_Custard_Syntax.dt_params with
                 | hd::tl -> true
                 | uu___2 -> false
               then is_poly st t.FStarC_Custard_Syntax.dt_name
               else false -> []
           | FStarC_Custard_Syntax.DType t when
               match t.FStarC_Custard_Syntax.dt_params with
               | hd::tl -> true
               | uu___2 -> false -> [FStarC_Custard_Syntax.DType t]
           | FStarC_Custard_Syntax.DType t ->
               let body =
                 match t.FStarC_Custard_Syntax.dt_body with
                 | FStarC_Custard_Syntax.TAbbrev c ->
                     let uu___2 = mono_cty st c in
                     FStarC_Custard_Syntax.TAbbrev uu___2
                 | FStarC_Custard_Syntax.TRecord fs ->
                     let uu___2 =
                       FStarC_List.map
                         (fun uu___3 ->
                            match uu___3 with
                            | (x, c) ->
                                let uu___4 = mono_cty st c in (x, uu___4)) fs in
                     FStarC_Custard_Syntax.TRecord uu___2
                 | FStarC_Custard_Syntax.TVariant cs ->
                     let uu___2 =
                       FStarC_List.map
                         (fun uu___3 ->
                            match uu___3 with
                            | (cn, fs) ->
                                let uu___4 =
                                  FStarC_List.map
                                    (fun uu___5 ->
                                       match uu___5 with
                                       | (x, c) ->
                                           let uu___6 = mono_cty st c in
                                           (x, uu___6)) fs in
                                (cn, uu___4)) cs in
                     FStarC_Custard_Syntax.TVariant uu___2
                 | FStarC_Custard_Syntax.TAbstract ->
                     FStarC_Custard_Syntax.TAbstract in
               [FStarC_Custard_Syntax.DType
                  {
                    FStarC_Custard_Syntax.dt_name =
                      (t.FStarC_Custard_Syntax.dt_name);
                    FStarC_Custard_Syntax.dt_params =
                      (t.FStarC_Custard_Syntax.dt_params);
                    FStarC_Custard_Syntax.dt_body = body;
                    FStarC_Custard_Syntax.dt_flags =
                      (t.FStarC_Custard_Syntax.dt_flags)
                  }]
           | FStarC_Custard_Syntax.DLet l ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_List.map
                       (fun b ->
                          let uu___5 =
                            mono_cty st b.FStarC_Custard_Syntax.b_ty in
                          {
                            FStarC_Custard_Syntax.b_name =
                              (b.FStarC_Custard_Syntax.b_name);
                            FStarC_Custard_Syntax.b_ty = uu___5
                          }) l.FStarC_Custard_Syntax.dl_binders in
                   let uu___5 = mono_cty st l.FStarC_Custard_Syntax.dl_ret in
                   let uu___6 =
                     let uu___7 =
                       FStarC_List.map
                         (fun b ->
                            ((b.FStarC_Custard_Syntax.b_name),
                              (b.FStarC_Custard_Syntax.b_ty)))
                         l.FStarC_Custard_Syntax.dl_binders in
                     mono_expr st uu___7 l.FStarC_Custard_Syntax.dl_body in
                   {
                     FStarC_Custard_Syntax.dl_name =
                       (l.FStarC_Custard_Syntax.dl_name);
                     FStarC_Custard_Syntax.dl_typars = [];
                     FStarC_Custard_Syntax.dl_binders = uu___4;
                     FStarC_Custard_Syntax.dl_ret = uu___5;
                     FStarC_Custard_Syntax.dl_eff =
                       (l.FStarC_Custard_Syntax.dl_eff);
                     FStarC_Custard_Syntax.dl_body = uu___6;
                     FStarC_Custard_Syntax.dl_flags =
                       (l.FStarC_Custard_Syntax.dl_flags)
                   } in
                 FStarC_Custard_Syntax.DLet uu___3 in
               [uu___2]
           | FStarC_Custard_Syntax.DExternal x when
               match x.FStarC_Custard_Syntax.dx_typars with
               | hd::tl -> true
               | uu___2 -> false -> [FStarC_Custard_Syntax.DExternal x]
           | FStarC_Custard_Syntax.DExternal x ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = mono_cty st x.FStarC_Custard_Syntax.dx_ty in
                   {
                     FStarC_Custard_Syntax.dx_name =
                       (x.FStarC_Custard_Syntax.dx_name);
                     FStarC_Custard_Syntax.dx_typars =
                       (x.FStarC_Custard_Syntax.dx_typars);
                     FStarC_Custard_Syntax.dx_ty = uu___4;
                     FStarC_Custard_Syntax.dx_target =
                       (x.FStarC_Custard_Syntax.dx_target);
                     FStarC_Custard_Syntax.dx_header =
                       (x.FStarC_Custard_Syntax.dx_header);
                     FStarC_Custard_Syntax.dx_flags =
                       (x.FStarC_Custard_Syntax.dx_flags)
                   } in
                 FStarC_Custard_Syntax.DExternal uu___3 in
               [uu___2]
           | FStarC_Custard_Syntax.DExn e ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_List.map (mono_cty st)
                       e.FStarC_Custard_Syntax.de_args in
                   {
                     FStarC_Custard_Syntax.de_name =
                       (e.FStarC_Custard_Syntax.de_name);
                     FStarC_Custard_Syntax.de_args = uu___4;
                     FStarC_Custard_Syntax.de_flags =
                       (e.FStarC_Custard_Syntax.de_flags)
                   } in
                 FStarC_Custard_Syntax.DExn uu___3 in
               [uu___2]) prog in
    drain st;
    (let rest1 =
       FStarC_List.collect
         (fun d ->
            match d with
            | FStarC_Custard_Syntax.DExternal x when
                match x.FStarC_Custard_Syntax.dx_typars with
                | hd::tl -> true
                | uu___3 -> false ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Custard_Syntax.string_of_name
                        x.FStarC_Custard_Syntax.dx_name in
                    FStarC_SMap.try_find st.ext_bare uu___5 in
                  match uu___4 with
                  | FStar_Pervasives_Native.None -> true
                  | uu___5 -> false in
                if uu___3
                then []
                else
                  (let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             FStarC_Custard_Syntax.string_of_name
                               x.FStarC_Custard_Syntax.dx_name in
                           Prims.strcat uu___8
                             " is polymorphic, and it is referred to with no type arguments, so there is no type to declare it at." in
                         Prims.strcat "Custard: the external " uu___7 in
                       FStar_Pprint.arbitrary_string uu___6 in
                     [uu___5;
                     FStar_Pprint.arbitrary_string
                       "A polymorphic external is emitted once per instantiation, and an instantiation comes from the type arguments on the reference to it.  With none, there is nothing to emit and the reference would name a symbol that does not exist.";
                     FStar_Pprint.arbitrary_string
                       "If this is a rule, put the argument's type on the EQual node it builds.  Otherwise give the declaration a monomorphic type."] in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Error_CustardPolyExternalUnused ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___4))
            | d1 -> [d1]) rest in
     let uu___3 =
       let uu___4 =
         let uu___5 =
           let uu___6 = FStarC_Effect.op_Bang st.ext_clones in
           FStarC_List.rev uu___6 in
         FStarC_List.map (fun d -> FStarC_Custard_Syntax.DExternal d) uu___5 in
       let uu___5 =
         let uu___6 =
           let uu___7 = FStarC_Effect.op_Bang st.clones in
           FStarC_List.rev uu___7 in
         FStarC_List.map (fun d -> FStarC_Custard_Syntax.DType d) uu___6 in
       FStarC_List.op_At uu___4 uu___5 in
     FStarC_List.op_At rest1 uu___3)))
