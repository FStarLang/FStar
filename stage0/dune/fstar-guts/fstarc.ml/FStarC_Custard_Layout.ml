open Prims
let layout_to_string (l : FStarC_Custard_Syntax.layout) : Prims.string=
  match l with
  | FStarC_Custard_Syntax.L_erased -> "erased"
  | FStarC_Custard_Syntax.L_newtype nt ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Custard_Syntax.showable_cty
                nt.FStarC_Custard_Syntax.nt_ty in
            Prims.strcat uu___3 ")" in
          Prims.strcat " : " uu___2 in
        Prims.strcat nt.FStarC_Custard_Syntax.nt_field uu___1 in
      Prims.strcat "newtype(" uu___
  | FStarC_Custard_Syntax.L_struct cs ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_nat
            (FStarC_List.length cs) in
        Prims.strcat uu___1 " ctors)" in
      Prims.strcat "struct(" uu___
  | FStarC_Custard_Syntax.L_abbrev c ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Custard_Syntax.showable_cty c in
        Prims.strcat uu___1 ")" in
      Prims.strcat "abbrev(" uu___
  | FStarC_Custard_Syntax.L_opaque -> "opaque"
type tbl =
  {
  types: FStarC_Custard_Syntax.dtype FStarC_SMap.t ;
  erased: Prims.bool FStarC_SMap.t ;
  layouts: FStarC_Custard_Syntax.layout FStarC_SMap.t ;
  ctors: (Prims.string * FStarC_Custard_Syntax.ctor_layout) FStarC_SMap.t ;
  pinned: unit FStarC_SMap.t ;
  fresh: Prims.int FStarC_Effect.ref }
let __proj__Mktbl__item__types (projectee : tbl) :
  FStarC_Custard_Syntax.dtype FStarC_SMap.t=
  match projectee with
  | { types; erased; layouts; ctors; pinned; fresh;_} -> types
let __proj__Mktbl__item__erased (projectee : tbl) : Prims.bool FStarC_SMap.t=
  match projectee with
  | { types; erased; layouts; ctors; pinned; fresh;_} -> erased
let __proj__Mktbl__item__layouts (projectee : tbl) :
  FStarC_Custard_Syntax.layout FStarC_SMap.t=
  match projectee with
  | { types; erased; layouts; ctors; pinned; fresh;_} -> layouts
let __proj__Mktbl__item__ctors (projectee : tbl) :
  (Prims.string * FStarC_Custard_Syntax.ctor_layout) FStarC_SMap.t=
  match projectee with
  | { types; erased; layouts; ctors; pinned; fresh;_} -> ctors
let __proj__Mktbl__item__pinned (projectee : tbl) : unit FStarC_SMap.t=
  match projectee with
  | { types; erased; layouts; ctors; pinned; fresh;_} -> pinned
let __proj__Mktbl__item__fresh (projectee : tbl) :
  Prims.int FStarC_Effect.ref=
  match projectee with
  | { types; erased; layouts; ctors; pinned; fresh;_} -> fresh
let key (n : FStarC_Custard_Syntax.name) : Prims.string=
  FStarC_Custard_Syntax.string_of_name n
let ctors_of_tydef (d : FStarC_Custard_Syntax.dtype) :
  (FStarC_Custard_Syntax.name * (Prims.string * FStarC_Custard_Syntax.cty)
    Prims.list) Prims.list=
  match d.FStarC_Custard_Syntax.dt_body with
  | FStarC_Custard_Syntax.TVariant cs -> cs
  | FStarC_Custard_Syntax.TRecord fs ->
      [((d.FStarC_Custard_Syntax.dt_name), fs)]
  | uu___ -> []
let rec cty_erased (t : tbl) (c : FStarC_Custard_Syntax.cty) : Prims.bool=
  match c with
  | FStarC_Custard_Syntax.TUnit -> true
  | FStarC_Custard_Syntax.TVar uu___ -> false
  | FStarC_Custard_Syntax.TAny -> false
  | FStarC_Custard_Syntax.TConst uu___ -> false
  | FStarC_Custard_Syntax.TExn -> false
  | FStarC_Custard_Syntax.TInt uu___ -> false
  | FStarC_Custard_Syntax.TFloat uu___ -> false
  | FStarC_Custard_Syntax.TArrow (uu___, e, r) ->
      if FStarC_Custard_Syntax.is_pure e then cty_erased t r else false
  | FStarC_Custard_Syntax.TTuple cs ->
      FStarC_List.for_all (fun c1 -> cty_erased t c1) cs
  | FStarC_Custard_Syntax.TBuf uu___ -> false
  | FStarC_Custard_Syntax.TRef uu___ -> false
  | FStarC_Custard_Syntax.TInline c1 -> cty_erased t c1
  | FStarC_Custard_Syntax.TApp (n, uu___) ->
      let uu___1 = let uu___2 = key n in FStarC_SMap.try_find t.erased uu___2 in
      (match uu___1 with
       | FStar_Pervasives_Native.Some b -> b
       | FStar_Pervasives_Native.None -> false)
let dtype_erased (t : tbl) (d : FStarC_Custard_Syntax.dtype) : Prims.bool=
  let uu___ =
    FStarC_Custard_Syntax.has_flag d.FStarC_Custard_Syntax.dt_flags
      FStarC_Custard_Syntax.Erased in
  if uu___
  then true
  else
    (let uu___1 =
       FStarC_Custard_Syntax.has_flag d.FStarC_Custard_Syntax.dt_flags
         FStarC_Custard_Syntax.Realized in
     if uu___1
     then false
     else
       (match d.FStarC_Custard_Syntax.dt_body with
        | FStarC_Custard_Syntax.TAbbrev c -> cty_erased t c
        | FStarC_Custard_Syntax.TRecord fs ->
            FStarC_List.for_all
              (fun uu___2 ->
                 match uu___2 with | (uu___3, c) -> cty_erased t c) fs
        | FStarC_Custard_Syntax.TVariant [] -> true
        | FStarC_Custard_Syntax.TVariant ((uu___2, fs)::[]) ->
            FStarC_List.for_all
              (fun uu___3 ->
                 match uu___3 with | (uu___4, c) -> cty_erased t c) fs
        | FStarC_Custard_Syntax.TVariant uu___2 -> false
        | FStarC_Custard_Syntax.TAbstract -> false))
let erasure_fixpoint (t : tbl) : unit=
  let step uu___ =
    let changed = FStarC_Effect.mk_ref false in
    FStarC_SMap.iter t.types
      (fun k d ->
         let old =
           let uu___2 = FStarC_SMap.try_find t.erased k in
           match uu___2 with
           | FStar_Pervasives_Native.Some b -> b
           | FStar_Pervasives_Native.None -> false in
         let uu___2 =
           let uu___3 = FStarC_SMap.try_find t.pinned k in
           match uu___3 with
           | FStar_Pervasives_Native.Some v -> true
           | uu___4 -> false in
         if uu___2
         then ()
         else
           (let nw = dtype_erased t d in
            if nw <> old
            then
              (FStarC_Effect.op_Colon_Equals changed true;
               FStarC_SMap.add t.erased k nw)
            else ()));
    FStarC_Effect.op_Bang changed in
  let rec loop fuel =
    if fuel <= Prims.int_zero
    then ()
    else
      (let uu___ = step () in
       if uu___ then loop (fuel - Prims.int_one) else ()) in
  let uu___ =
    FStarC_SMap.fold t.types (fun uu___1 uu___2 n -> n + Prims.int_one)
      Prims.int_one in
  loop uu___
let uninline (c : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.cty=
  match c with | FStarC_Custard_Syntax.TInline c1 -> c1 | c1 -> c1
let slots_of_fields (t : tbl)
  (fs : (Prims.string * FStarC_Custard_Syntax.cty) Prims.list) :
  (FStarC_Custard_Syntax.slot Prims.list * Prims.int * (Prims.string *
    FStarC_Custard_Syntax.cty) Prims.list)=
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 uu___2 ->
         match (uu___1, uu___2) with
         | ((slots, next, kept), (f, c)) ->
             let uu___3 = cty_erased t c in
             if uu___3
             then ((FStarC_Custard_Syntax.S_erased :: slots), next, kept)
             else
               (((FStarC_Custard_Syntax.S_at next) :: slots),
                 (next + Prims.int_one), ((f, c) :: kept)))
      ([], Prims.int_zero, []) fs in
  match uu___ with
  | (slots, next, kept) ->
      ((FStarC_List.rev slots), next, (FStarC_List.rev kept))
let ctor_layouts (t : tbl) (d : FStarC_Custard_Syntax.dtype) :
  FStarC_Custard_Syntax.ctor_layout Prims.list=
  let cs = ctors_of_tydef d in
  let single = (FStarC_List.length cs) = Prims.int_one in
  FStarC_List.mapi
    (fun i uu___ ->
       match uu___ with
       | (cn, fs) ->
           let uu___1 = slots_of_fields t fs in
           (match uu___1 with
            | (slots, arity, kept) ->
                {
                  FStarC_Custard_Syntax.cl_name = cn;
                  FStarC_Custard_Syntax.cl_tag =
                    (if single
                     then FStar_Pervasives_Native.None
                     else FStar_Pervasives_Native.Some i);
                  FStarC_Custard_Syntax.cl_slots = slots;
                  FStarC_Custard_Syntax.cl_arity = arity;
                  FStarC_Custard_Syntax.cl_fields = kept
                })) cs
let rec names_of_cty (c : FStarC_Custard_Syntax.cty) :
  Prims.string Prims.list=
  match c with
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = names_of_cty a in
      let uu___2 = names_of_cty b in FStarC_List.op_At uu___1 uu___2
  | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.collect names_of_cty cs
  | FStarC_Custard_Syntax.TBuf c1 -> names_of_cty c1
  | FStarC_Custard_Syntax.TRef c1 -> names_of_cty c1
  | FStarC_Custard_Syntax.TInline c1 -> names_of_cty c1
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ = key n in
      let uu___1 = FStarC_List.collect names_of_cty args in uu___ :: uu___1
  | uu___ -> []
let acyclic_candidates (cands : FStarC_Custard_Syntax.cty FStarC_SMap.t) :
  FStarC_Custard_Syntax.cty FStarC_SMap.t=
  let ok = FStarC_SMap.create (Prims.of_int 20) in
  FStarC_SMap.iter cands
    (fun k rep ->
       let seen = FStarC_SMap.create (Prims.of_int 10) in
       let rec go work =
         match work with
         | [] -> false
         | m::rest ->
             if m = k
             then true
             else
               (let uu___1 = FStarC_SMap.try_find seen m in
                match uu___1 with
                | FStar_Pervasives_Native.Some uu___2 -> go rest
                | FStar_Pervasives_Native.None ->
                    (FStarC_SMap.add seen m true;
                     (let uu___3 = FStarC_SMap.try_find cands m in
                      match uu___3 with
                      | FStar_Pervasives_Native.Some rep' ->
                          let uu___4 =
                            let uu___5 = names_of_cty rep' in
                            FStarC_List.op_At uu___5 rest in
                          go uu___4
                      | FStar_Pervasives_Native.None -> go rest))) in
       let uu___1 =
         let uu___2 = let uu___3 = names_of_cty rep in go uu___3 in
         Prims.not uu___2 in
       if uu___1 then FStarC_SMap.add ok k rep else ());
  ok
let compute_layouts (t : tbl) : unit=
  let cands = FStarC_SMap.create (Prims.of_int 20) in
  FStarC_SMap.iter t.types
    (fun k d ->
       let uu___1 =
         let uu___2 = FStarC_SMap.try_find t.pinned k in
         match uu___2 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___3 -> false in
       if uu___1
       then ()
       else
         (let erased =
            let uu___2 = FStarC_SMap.try_find t.erased k in
            match uu___2 with
            | FStar_Pervasives_Native.Some b -> b
            | FStar_Pervasives_Native.None -> false in
          if erased
          then FStarC_SMap.add t.layouts k FStarC_Custard_Syntax.L_erased
          else
            (match d.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TAbstract ->
                 FStarC_SMap.add t.layouts k FStarC_Custard_Syntax.L_opaque
             | FStarC_Custard_Syntax.TAbbrev c ->
                 FStarC_SMap.add t.layouts k
                   (FStarC_Custard_Syntax.L_abbrev c)
             | uu___2 ->
                 let cls = ctor_layouts t d in
                 (FStarC_SMap.add t.layouts k
                    (FStarC_Custard_Syntax.L_struct cls);
                  (let uu___4 =
                     let uu___5 =
                       FStarC_Custard_Syntax.has_flag
                         d.FStarC_Custard_Syntax.dt_flags
                         FStarC_Custard_Syntax.NoNewtype in
                     Prims.not uu___5 in
                   if uu___4
                   then
                     match cls with
                     | cl::[] ->
                         (if
                            cl.FStarC_Custard_Syntax.cl_arity = Prims.int_one
                          then
                            match cl.FStarC_Custard_Syntax.cl_fields with
                            | (uu___5, c)::[] ->
                                FStarC_SMap.add cands k (uninline c)
                            | uu___5 -> ()
                          else ())
                     | uu___5 -> ()
                   else ())))));
  (let cands1 = acyclic_candidates cands in
   FStarC_SMap.iter cands1
     (fun k uu___1 ->
        let uu___2 = FStarC_SMap.try_find t.layouts k in
        match uu___2 with
        | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_struct
            (cl::[])) ->
            let idx =
              let uu___3 =
                FStarC_List.fold_left
                  (fun uu___4 s ->
                     match uu___4 with
                     | (i, found) ->
                         (match (s, found) with
                          | (FStarC_Custard_Syntax.S_at uu___5,
                             FStar_Pervasives_Native.None) ->
                              ((i + Prims.int_one),
                                (FStar_Pervasives_Native.Some i))
                          | uu___5 -> ((i + Prims.int_one), found)))
                  (Prims.int_zero, FStar_Pervasives_Native.None)
                  cl.FStarC_Custard_Syntax.cl_slots in
              FStar_Pervasives_Native.snd uu___3 in
            (match (idx, (cl.FStarC_Custard_Syntax.cl_fields)) with
             | (FStar_Pervasives_Native.Some i, (f, c)::[]) ->
                 FStarC_SMap.add t.layouts k
                   (FStarC_Custard_Syntax.L_newtype
                      {
                        FStarC_Custard_Syntax.nt_ctor =
                          (cl.FStarC_Custard_Syntax.cl_name);
                        FStarC_Custard_Syntax.nt_field = f;
                        FStarC_Custard_Syntax.nt_index = i;
                        FStarC_Custard_Syntax.nt_ty = (uninline c)
                      })
             | uu___3 -> ())
        | uu___3 -> ()))
let register_ctors (t : tbl) : unit=
  FStarC_SMap.iter t.types
    (fun k d ->
       let uu___ =
         let uu___1 = FStarC_SMap.try_find t.pinned k in
         match uu___1 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___2 -> false in
       if uu___
       then ()
       else
         (let uu___1 = ctor_layouts t d in
          FStarC_List.iter
            (fun cl ->
               let uu___2 = key cl.FStarC_Custard_Syntax.cl_name in
               FStarC_SMap.add t.ctors uu___2 (k, cl)) uu___1))
let ctor_owner (t : tbl) (n : FStarC_Custard_Syntax.name) :
  (FStarC_Custard_Syntax.layout * FStarC_Custard_Syntax.ctor_layout)
    FStar_Pervasives_Native.option=
  let uu___ = let uu___1 = key n in FStarC_SMap.try_find t.ctors uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (owner, cl) ->
      let uu___1 = FStarC_SMap.try_find t.layouts owner in
      (match uu___1 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some l ->
           FStar_Pervasives_Native.Some (l, cl))
let rec resolve (t : tbl) (fuel : Prims.int) (c : FStarC_Custard_Syntax.cty)
  : FStarC_Custard_Syntax.cty=
  if fuel <= Prims.int_zero
  then c
  else
    (match c with
     | FStarC_Custard_Syntax.TArrow (a, e, b) ->
         let uu___ =
           let uu___1 = resolve t fuel a in
           let uu___2 = resolve t fuel b in (uu___1, e, uu___2) in
         FStarC_Custard_Syntax.TArrow uu___
     | FStarC_Custard_Syntax.TTuple cs ->
         let uu___ = FStarC_List.map (resolve t fuel) cs in
         FStarC_Custard_Syntax.TTuple uu___
     | FStarC_Custard_Syntax.TBuf c1 ->
         let uu___ = resolve t fuel c1 in FStarC_Custard_Syntax.TBuf uu___
     | FStarC_Custard_Syntax.TRef c1 ->
         let uu___ = resolve t fuel c1 in FStarC_Custard_Syntax.TRef uu___
     | FStarC_Custard_Syntax.TInline c1 ->
         let uu___ = resolve t fuel c1 in FStarC_Custard_Syntax.TInline uu___
     | FStarC_Custard_Syntax.TApp (n, args) ->
         let args1 = FStarC_List.map (resolve t fuel) args in
         let uu___ =
           let uu___1 = key n in FStarC_SMap.try_find t.layouts uu___1 in
         (match uu___ with
          | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_erased) ->
              FStarC_Custard_Syntax.TUnit
          | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_newtype nt)
              ->
              let params =
                let uu___1 =
                  let uu___2 = key n in FStarC_SMap.try_find t.types uu___2 in
                match uu___1 with
                | FStar_Pervasives_Native.Some d ->
                    d.FStarC_Custard_Syntax.dt_params
                | FStar_Pervasives_Native.None -> [] in
              let s =
                try
                  (fun uu___1 ->
                     match () with | () -> FStarC_List.zip params args1) ()
                with | uu___1 -> [] in
              let uu___1 =
                FStarC_Custard_Syntax.subst_cty s
                  nt.FStarC_Custard_Syntax.nt_ty in
              resolve t (fuel - Prims.int_one) uu___1
          | uu___1 ->
              let uu___2 =
                let uu___3 = key n in FStarC_SMap.try_find t.types uu___3 in
              (match uu___2 with
               | FStar_Pervasives_Native.Some d when
                   FStarC_Custard_Syntax.has_flag
                     d.FStarC_Custard_Syntax.dt_flags
                     FStarC_Custard_Syntax.Realized
                   -> FStarC_Custard_Syntax.TApp (n, args1)
               | FStar_Pervasives_Native.Some d ->
                   (match d.FStarC_Custard_Syntax.dt_body with
                    | FStarC_Custard_Syntax.TAbbrev c1 ->
                        let np =
                          FStarC_List.length
                            d.FStarC_Custard_Syntax.dt_params in
                        let uu___3 =
                          if (FStarC_List.length args1) > np
                          then FStarC_List.splitAt np args1
                          else (args1, []) in
                        (match uu___3 with
                         | (used, extra) ->
                             let s =
                               try
                                 (fun uu___4 ->
                                    match () with
                                    | () ->
                                        FStarC_List.zip
                                          d.FStarC_Custard_Syntax.dt_params
                                          used) ()
                               with | uu___4 -> [] in
                             let body = FStarC_Custard_Syntax.subst_cty s c1 in
                             let body1 =
                               match (extra, body) with
                               | ([], uu___4) -> body
                               | (uu___4, FStarC_Custard_Syntax.TApp (m, a))
                                   ->
                                   FStarC_Custard_Syntax.TApp
                                     (m, (FStarC_List.op_At a extra))
                               | uu___4 -> body in
                             resolve t (fuel - Prims.int_one) body1)
                    | uu___3 -> FStarC_Custard_Syntax.TApp (n, args1))
               | uu___3 -> FStarC_Custard_Syntax.TApp (n, args1)))
     | c1 -> c1)
let nth_opt (xs : 'a Prims.list) (i : Prims.int) :
  'a FStar_Pervasives_Native.option=
  let rec go xs1 i1 =
    match xs1 with
    | [] -> FStar_Pervasives_Native.None
    | x::xs2 ->
        if i1 <= Prims.int_zero
        then FStar_Pervasives_Native.Some x
        else go xs2 (i1 - Prims.int_one) in
  if i < Prims.int_zero then FStar_Pervasives_Native.None else go xs i
let keep_by_slots (slots : FStarC_Custard_Syntax.slot Prims.list)
  (xs : 'a Prims.list) : ('a Prims.list * 'a Prims.list)=
  let rec go slots1 xs1 kept dropped =
    match (slots1, xs1) with
    | (uu___, []) -> ((FStarC_List.rev kept), (FStarC_List.rev dropped))
    | ([], x::xs2) -> go [] xs2 (x :: kept) dropped
    | ((FStarC_Custard_Syntax.S_erased)::slots2, x::xs2) ->
        go slots2 xs2 kept (x :: dropped)
    | ((FStarC_Custard_Syntax.S_at uu___)::slots2, x::xs2) ->
        go slots2 xs2 (x :: kept) dropped in
  go slots xs [] []
let fresh_var (t : tbl) : Prims.string=
  (let uu___1 =
     let uu___2 = FStarC_Effect.op_Bang t.fresh in uu___2 + Prims.int_one in
   FStarC_Effect.op_Colon_Equals t.fresh uu___1);
  (let uu___1 = FStarC_Effect.op_Bang t.fresh in
   FStarC_Custard_Syntax.uniq "_dropped" uu___1)
let eta_ctors (t : tbl)
  (imports :
    (FStarC_Custard_Syntax.dtype * FStarC_Custard_Syntax.type_info)
      Prims.list)
  (prog : FStarC_Custard_Syntax.program) : FStarC_Custard_Syntax.program=
  let fields = FStarC_SMap.create (Prims.of_int 100) in
  let add d =
    let uu___ = ctors_of_tydef d in
    FStarC_List.iter
      (fun uu___1 ->
         match uu___1 with
         | (cn, fs) ->
             let uu___2 = key cn in FStarC_SMap.add fields uu___2 fs) uu___ in
  FStarC_List.iter (fun uu___1 -> match uu___1 with | (d, uu___2) -> add d)
    imports;
  FStarC_SMap.iter t.types (fun uu___2 d -> add d);
  (let rec drop n xs =
     if n <= Prims.int_zero
     then xs
     else
       (match xs with
        | [] -> []
        | uu___2::xs1 -> drop (n - Prims.int_one) xs1) in
   let fresh uu___2 =
     (let uu___4 =
        let uu___5 = FStarC_Effect.op_Bang t.fresh in uu___5 + Prims.int_one in
      FStarC_Effect.op_Colon_Equals t.fresh uu___4);
     (let uu___4 = FStarC_Effect.op_Bang t.fresh in
      FStarC_Custard_Syntax.uniq "_eta" uu___4) in
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
         let uu___2 =
           let uu___3 = key cn in FStarC_SMap.try_find fields uu___3 in
         (match uu___2 with
          | FStar_Pervasives_Native.Some fs when
              (FStarC_List.length es1) < (FStarC_List.length fs) ->
              let bs =
                let uu___3 = drop (FStarC_List.length es1) fs in
                FStarC_List.map
                  (fun uu___4 ->
                     match uu___4 with
                     | (f, c) ->
                         let uu___5 = fresh () in
                         {
                           FStarC_Custard_Syntax.b_name = uu___5;
                           FStarC_Custard_Syntax.b_ty = c
                         }) uu___3 in
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
                  (fun b c ->
                     FStarC_Custard_Syntax.TArrow
                       ((b.FStarC_Custard_Syntax.b_ty),
                         FStarC_Custard_Syntax.E_Pure, c)) bs
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
                     })) res FStarC_Custard_Syntax.E_Pure
          | uu___3 -> alt)
     | uu___2 -> FStarC_Custard_Syntax.map_children go x in
   FStarC_List.map
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DLet dl ->
            let uu___2 =
              let uu___3 = go dl.FStarC_Custard_Syntax.dl_body in
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
        | d1 -> d1) prog)
let hoist (dropped : FStarC_Custard_Syntax.expr Prims.list)
  (result : FStarC_Custard_Syntax.expr) : FStarC_Custard_Syntax.expr=
  FStarC_List.fold_right
    (fun d acc ->
       if FStarC_Custard_Syntax.is_pure d.FStarC_Custard_Syntax.eff
       then acc
       else
         {
           FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ESeq (d, acc));
           FStarC_Custard_Syntax.ty = (acc.FStarC_Custard_Syntax.ty);
           FStarC_Custard_Syntax.eff = (acc.FStarC_Custard_Syntax.eff)
         }) dropped result
let rec pat_vars (p : FStarC_Custard_Syntax.pat) : Prims.string Prims.list=
  match p with
  | FStarC_Custard_Syntax.PVar v -> [v]
  | FStarC_Custard_Syntax.PCtor (uu___, ps) ->
      FStarC_List.collect pat_vars ps
  | FStarC_Custard_Syntax.PTuple ps -> FStarC_List.collect pat_vars ps
  | FStarC_Custard_Syntax.POr ps -> FStarC_List.collect pat_vars ps
  | FStarC_Custard_Syntax.PRecord (uu___, fs) ->
      FStarC_List.collect
        (fun uu___1 -> match uu___1 with | (uu___2, q) -> pat_vars q) fs
  | FStarC_Custard_Syntax.PWild -> []
  | FStarC_Custard_Syntax.PConst uu___ -> []
let rec rw_pat (t : tbl) (p : FStarC_Custard_Syntax.pat) :
  (FStarC_Custard_Syntax.pat * Prims.string Prims.list)=
  let many ps =
    let ps1 = FStarC_List.map (rw_pat t) ps in
    let uu___ = FStarC_List.map FStar_Pervasives_Native.fst ps1 in
    let uu___1 = FStarC_List.collect FStar_Pervasives_Native.snd ps1 in
    (uu___, uu___1) in
  match p with
  | FStarC_Custard_Syntax.PCtor (n, ps) ->
      let uu___ = many ps in
      (match uu___ with
       | (ps1, freed) ->
           let uu___1 = ctor_owner t n in
           (match uu___1 with
            | FStar_Pervasives_Native.Some
                (FStarC_Custard_Syntax.L_erased, uu___2) ->
                let uu___3 =
                  let uu___4 = FStarC_List.collect pat_vars ps1 in
                  FStarC_List.op_At freed uu___4 in
                (FStarC_Custard_Syntax.PWild, uu___3)
            | FStar_Pervasives_Native.Some
                (FStarC_Custard_Syntax.L_newtype nt, uu___2) ->
                let uu___3 = nth_opt ps1 nt.FStarC_Custard_Syntax.nt_index in
                (match uu___3 with
                 | FStar_Pervasives_Native.Some p' ->
                     let others =
                       let uu___4 = FStarC_List.mapi (fun i q -> (i, q)) ps1 in
                       FStarC_List.collect
                         (fun uu___5 ->
                            match uu___5 with
                            | (i, q) ->
                                if i = nt.FStarC_Custard_Syntax.nt_index
                                then []
                                else pat_vars q) uu___4 in
                     (p', (FStarC_List.op_At freed others))
                 | FStar_Pervasives_Native.None ->
                     let uu___4 =
                       let uu___5 = FStarC_List.collect pat_vars ps1 in
                       FStarC_List.op_At freed uu___5 in
                     (FStarC_Custard_Syntax.PWild, uu___4))
            | FStar_Pervasives_Native.Some (uu___2, cl) ->
                let uu___3 =
                  keep_by_slots cl.FStarC_Custard_Syntax.cl_slots ps1 in
                (match uu___3 with
                 | (kept, dropped) ->
                     let uu___4 =
                       let uu___5 = FStarC_List.collect pat_vars dropped in
                       FStarC_List.op_At freed uu___5 in
                     ((FStarC_Custard_Syntax.PCtor (n, kept)), uu___4))
            | FStar_Pervasives_Native.None ->
                ((FStarC_Custard_Syntax.PCtor (n, ps1)), freed)))
  | FStarC_Custard_Syntax.PRecord (n, fs) ->
      let qs =
        FStarC_List.map
          (fun uu___ ->
             match uu___ with
             | (f, q) -> let uu___1 = rw_pat t q in (f, uu___1)) fs in
      let fs1 =
        FStarC_List.map
          (fun uu___ -> match uu___ with | (f, (q, uu___1)) -> (f, q)) qs in
      let freed =
        FStarC_List.collect
          (fun uu___ -> match uu___ with | (uu___1, (uu___2, vs)) -> vs) qs in
      let others keep =
        FStarC_List.collect
          (fun uu___ ->
             match uu___ with
             | (f, q) ->
                 let uu___1 = keep f in if uu___1 then [] else pat_vars q)
          fs1 in
      let uu___ = let uu___1 = key n in FStarC_SMap.try_find t.layouts uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_erased) ->
           let uu___1 =
             let uu___2 = others (fun uu___3 -> false) in
             FStarC_List.op_At freed uu___2 in
           (FStarC_Custard_Syntax.PWild, uu___1)
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_newtype nt) ->
           let uu___1 =
             FStarC_List.tryFind
               (fun uu___2 ->
                  match uu___2 with
                  | (f, uu___3) -> f = nt.FStarC_Custard_Syntax.nt_field) fs1 in
           (match uu___1 with
            | FStar_Pervasives_Native.Some (uu___2, q) ->
                let uu___3 =
                  let uu___4 =
                    others (fun f -> f = nt.FStarC_Custard_Syntax.nt_field) in
                  FStarC_List.op_At freed uu___4 in
                (q, uu___3)
            | FStar_Pervasives_Native.None ->
                let uu___2 =
                  let uu___3 = others (fun uu___4 -> false) in
                  FStarC_List.op_At freed uu___3 in
                (FStarC_Custard_Syntax.PWild, uu___2))
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_struct
           (cl::[])) ->
           let keep f =
             FStarC_List.existsb
               (fun uu___1 -> match uu___1 with | (g, uu___2) -> g = f)
               cl.FStarC_Custard_Syntax.cl_fields in
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 FStarC_List.filter
                   (fun uu___4 -> match uu___4 with | (f, uu___5) -> keep f)
                   fs1 in
               (n, uu___3) in
             FStarC_Custard_Syntax.PRecord uu___2 in
           let uu___2 =
             let uu___3 = others keep in FStarC_List.op_At freed uu___3 in
           (uu___1, uu___2)
       | uu___1 -> ((FStarC_Custard_Syntax.PRecord (n, fs1)), freed))
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = many ps in
      (match uu___ with
       | (ps1, freed) -> ((FStarC_Custard_Syntax.PTuple ps1), freed))
  | FStarC_Custard_Syntax.POr ps ->
      let uu___ = many ps in
      (match uu___ with
       | (ps1, freed) -> ((FStarC_Custard_Syntax.POr ps1), freed))
  | p1 -> (p1, [])
let rec rw_expr (t : tbl) (x : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  let ty = resolve t (Prims.of_int 100) x.FStarC_Custard_Syntax.ty in
  let x1 =
    {
      FStarC_Custard_Syntax.e = (x.FStarC_Custard_Syntax.e);
      FStarC_Custard_Syntax.ty = ty;
      FStarC_Custard_Syntax.eff = (x.FStarC_Custard_Syntax.eff)
    } in
  match x1.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst uu___ -> x1
  | FStarC_Custard_Syntax.EVar uu___ -> x1
  | FStarC_Custard_Syntax.EAny -> x1
  | FStarC_Custard_Syntax.EAbort uu___ -> x1
  | FStarC_Custard_Syntax.EQual (n, cs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (resolve t (Prims.of_int 100)) cs in
          (n, uu___2) in
        FStarC_Custard_Syntax.EQual uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ELet (v, c, e1, e2) ->
      let uu___ =
        let uu___1 =
          let uu___2 = resolve t (Prims.of_int 100) c in
          let uu___3 = rw_expr t e1 in
          let uu___4 = rw_expr t e2 in (v, uu___2, uu___3, uu___4) in
        FStarC_Custard_Syntax.ELet uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EApp (h, args) ->
      let uu___ =
        let uu___1 =
          let uu___2 = rw_expr t h in
          let uu___3 = FStarC_List.map (rw_expr t) args in (uu___2, uu___3) in
        FStarC_Custard_Syntax.EApp uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EFun (bs, b) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.map
              (fun b1 ->
                 let uu___3 =
                   resolve t (Prims.of_int 100) b1.FStarC_Custard_Syntax.b_ty in
                 {
                   FStarC_Custard_Syntax.b_name =
                     (b1.FStarC_Custard_Syntax.b_name);
                   FStarC_Custard_Syntax.b_ty = uu___3
                 }) bs in
          let uu___3 = rw_expr t b in (uu___2, uu___3) in
        FStarC_Custard_Syntax.EFun uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EMatch (s, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = rw_expr t s in
          let uu___3 = FStarC_List.map (rw_branch t) brs in (uu___2, uu___3) in
        FStarC_Custard_Syntax.EMatch uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EIf (c, a, b) ->
      let uu___ =
        let uu___1 =
          let uu___2 = rw_expr t c in
          let uu___3 = rw_expr t a in
          let uu___4 = rw_expr t b in (uu___2, uu___3, uu___4) in
        FStarC_Custard_Syntax.EIf uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ESeq (a, b) ->
      let uu___ =
        let uu___1 =
          let uu___2 = rw_expr t a in
          let uu___3 = rw_expr t b in (uu___2, uu___3) in
        FStarC_Custard_Syntax.ESeq uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ETuple es ->
      let uu___ =
        let uu___1 = FStarC_List.map (rw_expr t) es in
        FStarC_Custard_Syntax.ETuple uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EOp (o, es) ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (rw_expr t) es in (o, uu___2) in
        FStarC_Custard_Syntax.EOp uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.EWhile (a, b) ->
      let uu___ =
        let uu___1 =
          let uu___2 = rw_expr t a in
          let uu___3 = rw_expr t b in (uu___2, uu___3) in
        FStarC_Custard_Syntax.EWhile uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ERaise e1 ->
      let uu___ =
        let uu___1 = rw_expr t e1 in FStarC_Custard_Syntax.ERaise uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ETry (a, brs) ->
      let uu___ =
        let uu___1 =
          let uu___2 = rw_expr t a in
          let uu___3 = FStarC_List.map (rw_branch t) brs in (uu___2, uu___3) in
        FStarC_Custard_Syntax.ETry uu___1 in
      {
        FStarC_Custard_Syntax.e = uu___;
        FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
        FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
      }
  | FStarC_Custard_Syntax.ECtor (n, es) ->
      let es1 = FStarC_List.map (rw_expr t) es in
      let uu___ = ctor_owner t n in
      (match uu___ with
       | FStar_Pervasives_Native.Some
           (FStarC_Custard_Syntax.L_erased, uu___1) ->
           hoist es1
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.e);
               FStarC_Custard_Syntax.ty =
                 (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
             }
       | FStar_Pervasives_Native.Some
           (FStarC_Custard_Syntax.L_newtype nt, uu___1) ->
           let uu___2 = nth_opt es1 nt.FStarC_Custard_Syntax.nt_index in
           (match uu___2 with
            | FStar_Pervasives_Native.Some payload ->
                let dropped =
                  let uu___3 = FStarC_List.mapi (fun i e -> (i, e)) es1 in
                  FStarC_List.collect
                    (fun uu___4 ->
                       match uu___4 with
                       | (i, e) ->
                           if i = nt.FStarC_Custard_Syntax.nt_index
                           then []
                           else [e]) uu___3 in
                hoist dropped payload
            | FStar_Pervasives_Native.None ->
                hoist es1
                  {
                    FStarC_Custard_Syntax.e =
                      (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.e);
                    FStarC_Custard_Syntax.ty =
                      (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff =
                      (x1.FStarC_Custard_Syntax.eff)
                  })
       | FStar_Pervasives_Native.Some (uu___1, cl) ->
           let uu___2 = keep_by_slots cl.FStarC_Custard_Syntax.cl_slots es1 in
           (match uu___2 with
            | (kept, dropped) ->
                hoist dropped
                  {
                    FStarC_Custard_Syntax.e =
                      (FStarC_Custard_Syntax.ECtor (n, kept));
                    FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff =
                      (x1.FStarC_Custard_Syntax.eff)
                  })
       | FStar_Pervasives_Native.None ->
           {
             FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ECtor (n, es1));
             FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.ERecord (n, fs) ->
      let fs1 =
        FStarC_List.map
          (fun uu___ ->
             match uu___ with
             | (f, e) -> let uu___1 = rw_expr t e in (f, uu___1)) fs in
      let uu___ = let uu___1 = key n in FStarC_SMap.try_find t.layouts uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_erased) ->
           let uu___1 = FStarC_List.map FStar_Pervasives_Native.snd fs1 in
           hoist uu___1
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.e);
               FStarC_Custard_Syntax.ty =
                 (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
             }
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_newtype nt) ->
           let uu___1 =
             FStarC_List.tryFind
               (fun uu___2 ->
                  match uu___2 with
                  | (f, uu___3) -> f = nt.FStarC_Custard_Syntax.nt_field) fs1 in
           (match uu___1 with
            | FStar_Pervasives_Native.Some (uu___2, payload) ->
                let uu___3 =
                  FStarC_List.collect
                    (fun uu___4 ->
                       match uu___4 with
                       | (f, e) ->
                           if f = nt.FStarC_Custard_Syntax.nt_field
                           then []
                           else [e]) fs1 in
                hoist uu___3 payload
            | FStar_Pervasives_Native.None ->
                let uu___2 = FStarC_List.map FStar_Pervasives_Native.snd fs1 in
                hoist uu___2
                  {
                    FStarC_Custard_Syntax.e =
                      (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.e);
                    FStarC_Custard_Syntax.ty =
                      (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff =
                      (x1.FStarC_Custard_Syntax.eff)
                  })
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_struct
           (cl::[])) ->
           let keep f =
             FStarC_List.existsb
               (fun uu___1 -> match uu___1 with | (g, uu___2) -> g = f)
               cl.FStarC_Custard_Syntax.cl_fields in
           let kept =
             FStarC_List.collect
               (fun uu___1 ->
                  match uu___1 with
                  | (f, e) ->
                      let uu___2 = keep f in if uu___2 then [(f, e)] else [])
               fs1 in
           let dropped =
             FStarC_List.collect
               (fun uu___1 ->
                  match uu___1 with
                  | (f, e) ->
                      let uu___2 = keep f in if uu___2 then [] else [e]) fs1 in
           hoist dropped
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.ERecord (n, kept));
               FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
             }
       | uu___1 ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.ERecord (n, fs1));
             FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.EProj (e1, n, f) ->
      let e11 = rw_expr t e1 in
      let uu___ = ctor_owner t n in
      (match uu___ with
       | FStar_Pervasives_Native.Some
           (FStarC_Custard_Syntax.L_erased, uu___1) ->
           hoist [e11]
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.e);
               FStarC_Custard_Syntax.ty =
                 (FStarC_Custard_Syntax.unit_expr.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
             }
       | FStar_Pervasives_Native.Some
           (FStarC_Custard_Syntax.L_newtype uu___1, uu___2) -> e11
       | uu___1 ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EProj (e11, n, f));
             FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.EDiscrim (e1, n) ->
      let e11 = rw_expr t e1 in
      let uu___ = ctor_owner t n in
      (match uu___ with
       | FStar_Pervasives_Native.Some (uu___1, cl) when
           match cl.FStarC_Custard_Syntax.cl_tag with
           | FStar_Pervasives_Native.None -> true
           | uu___2 -> false ->
           hoist [e11]
             {
               FStarC_Custard_Syntax.e =
                 (FStarC_Custard_Syntax.EConst
                    (FStarC_Custard_Syntax.CBool true));
               FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
               FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
             }
       | uu___1 ->
           {
             FStarC_Custard_Syntax.e =
               (FStarC_Custard_Syntax.EDiscrim (e11, n));
             FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
             FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
           })
  | FStarC_Custard_Syntax.ECoerce (e1, c) ->
      let c1 = resolve t (Prims.of_int 100) c in
      let e11 = rw_expr t e1 in
      let e12 =
        match e11.FStarC_Custard_Syntax.e with
        | FStarC_Custard_Syntax.ECoerce (e2, uu___) -> e2
        | uu___ -> e11 in
      if e12.FStarC_Custard_Syntax.ty = c1
      then e12
      else
        {
          FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ECoerce (e12, c1));
          FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
        }
  | FStarC_Custard_Syntax.ECast (e1, c) ->
      let c1 = resolve t (Prims.of_int 100) c in
      let e11 = rw_expr t e1 in
      if e11.FStarC_Custard_Syntax.ty = c1
      then e11
      else
        {
          FStarC_Custard_Syntax.e = (FStarC_Custard_Syntax.ECast (e11, c1));
          FStarC_Custard_Syntax.ty = (x1.FStarC_Custard_Syntax.ty);
          FStarC_Custard_Syntax.eff = (x1.FStarC_Custard_Syntax.eff)
        }
and rw_branch (t : tbl) (br : FStarC_Custard_Syntax.branch) :
  FStarC_Custard_Syntax.branch=
  let uu___ = br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 = rw_pat t p in
      (match uu___1 with
       | (p1, freed) ->
           let bind e =
             FStarC_List.fold_right
               (fun v acc ->
                  {
                    FStarC_Custard_Syntax.e =
                      (FStarC_Custard_Syntax.ELet
                         (v, FStarC_Custard_Syntax.TUnit,
                           FStarC_Custard_Syntax.unit_expr, acc));
                    FStarC_Custard_Syntax.ty = (acc.FStarC_Custard_Syntax.ty);
                    FStarC_Custard_Syntax.eff =
                      (acc.FStarC_Custard_Syntax.eff)
                  }) freed e in
           let uu___2 =
             match g with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some g1 ->
                 let uu___3 = let uu___4 = rw_expr t g1 in bind uu___4 in
                 FStar_Pervasives_Native.Some uu___3 in
           let uu___3 = let uu___4 = rw_expr t b in bind uu___4 in
           (p1, uu___2, uu___3))
let rec cty_vars (c : FStarC_Custard_Syntax.cty) : Prims.string Prims.list=
  match c with
  | FStarC_Custard_Syntax.TVar x -> [x]
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = cty_vars a in
      let uu___2 = cty_vars b in FStarC_List.op_At uu___1 uu___2
  | FStarC_Custard_Syntax.TApp (uu___, args) ->
      FStarC_List.collect cty_vars args
  | FStarC_Custard_Syntax.TBuf c1 -> cty_vars c1
  | FStarC_Custard_Syntax.TInline c1 -> cty_vars c1
  | FStarC_Custard_Syntax.TRef c1 -> cty_vars c1
  | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.collect cty_vars cs
  | uu___ -> []
let rec cty_names (c : FStarC_Custard_Syntax.cty) : Prims.string Prims.list=
  match c with
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = cty_names a in
      let uu___2 = cty_names b in FStarC_List.op_At uu___1 uu___2
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ = key n in
      let uu___1 = FStarC_List.collect cty_names args in uu___ :: uu___1
  | FStarC_Custard_Syntax.TBuf c1 -> cty_names c1
  | FStarC_Custard_Syntax.TInline c1 -> cty_names c1
  | FStarC_Custard_Syntax.TRef c1 -> cty_names c1
  | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.collect cty_names cs
  | uu___ -> []
let collapsed_abbrev (dt : FStarC_Custard_Syntax.dtype)
  (payload : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.decl FStar_Pervasives_Native.option=
  let vars = cty_vars payload in
  let uu___ =
    let uu___1 =
      FStarC_List.for_all (fun p -> FStarC_List.mem p vars)
        dt.FStarC_Custard_Syntax.dt_params in
    if uu___1
    then
      let uu___2 =
        let uu___3 = key dt.FStarC_Custard_Syntax.dt_name in
        let uu___4 = cty_names payload in FStarC_List.mem uu___3 uu___4 in
      Prims.not uu___2
    else false in
  if uu___
  then
    FStar_Pervasives_Native.Some
      (FStarC_Custard_Syntax.DType
         {
           FStarC_Custard_Syntax.dt_name = (dt.FStarC_Custard_Syntax.dt_name);
           FStarC_Custard_Syntax.dt_params =
             (dt.FStarC_Custard_Syntax.dt_params);
           FStarC_Custard_Syntax.dt_body =
             (FStarC_Custard_Syntax.TAbbrev payload);
           FStarC_Custard_Syntax.dt_flags =
             (dt.FStarC_Custard_Syntax.dt_flags)
         })
  else FStar_Pervasives_Native.None
let rw_decl (t : tbl) (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl Prims.list=
  match d with
  | FStarC_Custard_Syntax.DType dt ->
      let k = key dt.FStarC_Custard_Syntax.dt_name in
      let uu___ = FStarC_SMap.try_find t.layouts k in
      (match uu___ with
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_erased) -> []
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_newtype nt) ->
           let uu___1 =
             let uu___2 =
               resolve t (Prims.of_int 100) nt.FStarC_Custard_Syntax.nt_ty in
             collapsed_abbrev dt uu___2 in
           (match uu___1 with
            | FStar_Pervasives_Native.Some d1 -> [d1]
            | FStar_Pervasives_Native.None -> [])
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_struct cls) ->
           let body =
             match dt.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TRecord uu___1 ->
                 (match cls with
                  | cl::[] ->
                      let uu___2 =
                        FStarC_List.map
                          (fun uu___3 ->
                             match uu___3 with
                             | (f, c) ->
                                 let uu___4 = resolve t (Prims.of_int 100) c in
                                 (f, uu___4))
                          cl.FStarC_Custard_Syntax.cl_fields in
                      FStarC_Custard_Syntax.TRecord uu___2
                  | uu___2 -> dt.FStarC_Custard_Syntax.dt_body)
             | FStarC_Custard_Syntax.TVariant uu___1 ->
                 let uu___2 =
                   FStarC_List.map
                     (fun cl ->
                        let uu___3 =
                          FStarC_List.map
                            (fun uu___4 ->
                               match uu___4 with
                               | (f, c) ->
                                   let uu___5 =
                                     resolve t (Prims.of_int 100) c in
                                   (f, uu___5))
                            cl.FStarC_Custard_Syntax.cl_fields in
                        ((cl.FStarC_Custard_Syntax.cl_name), uu___3)) cls in
                 FStarC_Custard_Syntax.TVariant uu___2
             | b -> b in
           [FStarC_Custard_Syntax.DType
              {
                FStarC_Custard_Syntax.dt_name =
                  (dt.FStarC_Custard_Syntax.dt_name);
                FStarC_Custard_Syntax.dt_params =
                  (dt.FStarC_Custard_Syntax.dt_params);
                FStarC_Custard_Syntax.dt_body = body;
                FStarC_Custard_Syntax.dt_flags =
                  (dt.FStarC_Custard_Syntax.dt_flags)
              }]
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.L_abbrev c) ->
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 = resolve t (Prims.of_int 100) c in
                 FStarC_Custard_Syntax.TAbbrev uu___4 in
               {
                 FStarC_Custard_Syntax.dt_name =
                   (dt.FStarC_Custard_Syntax.dt_name);
                 FStarC_Custard_Syntax.dt_params =
                   (dt.FStarC_Custard_Syntax.dt_params);
                 FStarC_Custard_Syntax.dt_body = uu___3;
                 FStarC_Custard_Syntax.dt_flags =
                   (dt.FStarC_Custard_Syntax.dt_flags)
               } in
             FStarC_Custard_Syntax.DType uu___2 in
           [uu___1]
       | uu___1 -> [FStarC_Custard_Syntax.DType dt])
  | FStarC_Custard_Syntax.DLet dl ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.map
              (fun b ->
                 let uu___3 =
                   resolve t (Prims.of_int 100) b.FStarC_Custard_Syntax.b_ty in
                 {
                   FStarC_Custard_Syntax.b_name =
                     (b.FStarC_Custard_Syntax.b_name);
                   FStarC_Custard_Syntax.b_ty = uu___3
                 }) dl.FStarC_Custard_Syntax.dl_binders in
          let uu___3 =
            resolve t (Prims.of_int 100) dl.FStarC_Custard_Syntax.dl_ret in
          let uu___4 = rw_expr t dl.FStarC_Custard_Syntax.dl_body in
          {
            FStarC_Custard_Syntax.dl_name =
              (dl.FStarC_Custard_Syntax.dl_name);
            FStarC_Custard_Syntax.dl_typars =
              (dl.FStarC_Custard_Syntax.dl_typars);
            FStarC_Custard_Syntax.dl_binders = uu___2;
            FStarC_Custard_Syntax.dl_ret = uu___3;
            FStarC_Custard_Syntax.dl_eff = (dl.FStarC_Custard_Syntax.dl_eff);
            FStarC_Custard_Syntax.dl_body = uu___4;
            FStarC_Custard_Syntax.dl_flags =
              (dl.FStarC_Custard_Syntax.dl_flags)
          } in
        FStarC_Custard_Syntax.DLet uu___1 in
      [uu___]
  | FStarC_Custard_Syntax.DExternal dx ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            resolve t (Prims.of_int 100) dx.FStarC_Custard_Syntax.dx_ty in
          {
            FStarC_Custard_Syntax.dx_name =
              (dx.FStarC_Custard_Syntax.dx_name);
            FStarC_Custard_Syntax.dx_typars =
              (dx.FStarC_Custard_Syntax.dx_typars);
            FStarC_Custard_Syntax.dx_ty = uu___2;
            FStarC_Custard_Syntax.dx_target =
              (dx.FStarC_Custard_Syntax.dx_target);
            FStarC_Custard_Syntax.dx_header =
              (dx.FStarC_Custard_Syntax.dx_header);
            FStarC_Custard_Syntax.dx_flags =
              (dx.FStarC_Custard_Syntax.dx_flags)
          } in
        FStarC_Custard_Syntax.DExternal uu___1 in
      [uu___]
  | FStarC_Custard_Syntax.DExn de ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.map (resolve t (Prims.of_int 100))
              de.FStarC_Custard_Syntax.de_args in
          {
            FStarC_Custard_Syntax.de_name =
              (de.FStarC_Custard_Syntax.de_name);
            FStarC_Custard_Syntax.de_args = uu___2;
            FStarC_Custard_Syntax.de_flags =
              (de.FStarC_Custard_Syntax.de_flags)
          } in
        FStarC_Custard_Syntax.DExn uu___1 in
      [uu___]
let record_verdict (dt : FStarC_Custard_Syntax.dtype) : Prims.bool=
  let uu___ =
    FStarC_Custard_Syntax.has_flag dt.FStarC_Custard_Syntax.dt_flags
      FStarC_Custard_Syntax.Realized in
  if uu___
  then
    FStarC_Custard_Syntax.has_flag dt.FStarC_Custard_Syntax.dt_flags
      FStarC_Custard_Syntax.SourceRecord
  else
    (match dt.FStarC_Custard_Syntax.dt_body with
     | FStarC_Custard_Syntax.TVariant ((uu___1, fs)::[]) ->
         (match fs with | hd::tl -> true | uu___2 -> false)
     | uu___1 -> false)
let positional (f : Prims.string) : Prims.bool=
  if (FStarC_String.strlen f) > Prims.int_one
  then
    let uu___ = FStarC_String.substring f Prims.int_zero Prims.int_one in
    uu___ = "_"
  else false
let record_body
  (look :
    FStarC_Custard_Syntax.name ->
      FStarC_Custard_Syntax.dtype FStar_Pervasives_Native.option)
  (n : FStarC_Custard_Syntax.name) :
  (Prims.string Prims.list * FStarC_Custard_Syntax.name
    FStar_Pervasives_Native.option * (Prims.string *
    FStarC_Custard_Syntax.cty) Prims.list) FStar_Pervasives_Native.option=
  let uu___ = look n in
  match uu___ with
  | FStar_Pervasives_Native.Some t ->
      (match t.FStarC_Custard_Syntax.dt_body with
       | FStarC_Custard_Syntax.TRecord fs ->
           if (match fs with | hd::tl -> true | uu___1 -> false)
           then
             FStar_Pervasives_Native.Some
               ((t.FStarC_Custard_Syntax.dt_params),
                 FStar_Pervasives_Native.None, fs)
           else FStar_Pervasives_Native.None
       | FStarC_Custard_Syntax.TVariant ((cn, fs)::[]) ->
           if (match fs with | hd::tl -> true | uu___1 -> false)
           then
             FStar_Pervasives_Native.Some
               ((t.FStarC_Custard_Syntax.dt_params),
                 (FStar_Pervasives_Native.Some cn), fs)
           else FStar_Pervasives_Native.None
       | uu___1 -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let strip_inline (c : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.cty=
  match c with | FStarC_Custard_Syntax.TInline c1 -> c1 | c1 -> c1
let rec ctor_plan
  (look :
    FStarC_Custard_Syntax.name ->
      FStarC_Custard_Syntax.dtype FStar_Pervasives_Native.option)
  (seen : Prims.string Prims.list)
  (fs : (Prims.string * FStarC_Custard_Syntax.cty) Prims.list) :
  FStarC_Custard_Syntax.fplan=
  let allpos =
    FStarC_List.for_all
      (fun uu___ -> match uu___ with | (f, uu___1) -> positional f) fs in
  let next = FStarC_SMap.create Prims.int_one in
  let fresh f g =
    if allpos
    then
      let i =
        let uu___ = FStarC_SMap.try_find next "n" in
        match uu___ with
        | FStar_Pervasives_Native.Some i1 -> i1
        | FStar_Pervasives_Native.None -> Prims.int_zero in
      (FStarC_SMap.add next "n" (i + Prims.int_one);
       Prims.strcat "_" (Prims.string_of_int i))
    else if g = "" then f else Prims.strcat f (Prims.strcat "_" g) in
  FStarC_List.map
    (fun uu___ ->
       match uu___ with
       | (f, c) ->
           (match c with
            | FStarC_Custard_Syntax.TInline (FStarC_Custard_Syntax.TApp
                (rn, args)) when
                let uu___1 =
                  FStarC_List.existsb
                    (fun k -> let uu___2 = key rn in k = uu___2) seen in
                Prims.not uu___1 ->
                let uu___1 =
                  let uu___2 = let uu___3 = key rn in uu___3 :: seen in
                  expanded_body look uu___2 rn args in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some (rc, src) ->
                     let dst =
                       FStarC_List.map
                         (fun uu___2 ->
                            match uu___2 with
                            | (g, gt) ->
                                let uu___3 = fresh f g in (uu___3, gt)) src in
                     (f, f,
                       (FStar_Pervasives_Native.Some
                          {
                            FStarC_Custard_Syntax.ex_ty =
                              (FStarC_Custard_Syntax.TApp (rn, args));
                            FStarC_Custard_Syntax.ex_type = rn;
                            FStarC_Custard_Syntax.ex_ctor = rc;
                            FStarC_Custard_Syntax.ex_src = src;
                            FStarC_Custard_Syntax.ex_dst = dst
                          }))
                 | FStar_Pervasives_Native.None ->
                     let uu___2 = fresh f "" in
                     (f, uu___2, FStar_Pervasives_Native.None))
            | uu___1 ->
                let uu___2 = fresh f "" in
                (f, uu___2, FStar_Pervasives_Native.None))) fs
and expanded_body
  (look :
    FStarC_Custard_Syntax.name ->
      FStarC_Custard_Syntax.dtype FStar_Pervasives_Native.option)
  (seen : Prims.string Prims.list) (rn : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.cty Prims.list) :
  (FStarC_Custard_Syntax.name FStar_Pervasives_Native.option * (Prims.string
    * FStarC_Custard_Syntax.cty) Prims.list) FStar_Pervasives_Native.option=
  let uu___ = record_body look rn in
  match uu___ with
  | FStar_Pervasives_Native.Some (ps, rc, rfs) ->
      if (FStarC_List.length ps) <> (FStarC_List.length args)
      then FStar_Pervasives_Native.None
      else
        (let sm = FStarC_List.zip ps args in
         let rfs1 =
           FStarC_List.map
             (fun uu___1 ->
                match uu___1 with
                | (g, gt) ->
                    let uu___2 = FStarC_Custard_Syntax.subst_cty sm gt in
                    (g, uu___2)) rfs in
         let uu___1 =
           let uu___2 =
             FStarC_List.existsb
               (fun uu___3 ->
                  match uu___3 with
                  | (uu___4, c) ->
                      (match c with
                       | FStarC_Custard_Syntax.TInline _0 -> true
                       | uu___5 -> false)) rfs1 in
           Prims.not uu___2 in
         if uu___1
         then FStar_Pervasives_Native.Some (rc, rfs1)
         else
           (let pl = ctor_plan look seen rfs1 in
            let uu___2 =
              let uu___3 =
                FStarC_List.collect
                  (fun uu___4 ->
                     match uu___4 with
                     | ((uu___5, c), (uu___6, g', ex)) ->
                         (match ex with
                          | FStar_Pervasives_Native.Some ex1 ->
                              ex1.FStarC_Custard_Syntax.ex_dst
                          | FStar_Pervasives_Native.None ->
                              [(g', (strip_inline c))]))
                  (FStarC_List.zip rfs1 pl) in
              (rc, uu___3) in
            FStar_Pervasives_Native.Some uu___2))
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ctor_plans
  (look :
    FStarC_Custard_Syntax.name ->
      FStarC_Custard_Syntax.dtype FStar_Pervasives_Native.option)
  (dt : FStarC_Custard_Syntax.dtype) :
  (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.fplan) Prims.list=
  let uu___ =
    FStarC_Custard_Syntax.has_flag dt.FStarC_Custard_Syntax.dt_flags
      FStarC_Custard_Syntax.Realized in
  if uu___
  then []
  else
    (match dt.FStarC_Custard_Syntax.dt_body with
     | FStarC_Custard_Syntax.TVariant cs ->
         FStarC_List.collect
           (fun uu___1 ->
              match uu___1 with
              | (cn, fs) ->
                  let uu___2 =
                    let uu___3 =
                      FStarC_List.existsb
                        (fun uu___4 ->
                           match uu___4 with
                           | (uu___5, c) ->
                               (match c with
                                | FStarC_Custard_Syntax.TInline _0 -> true
                                | uu___6 -> false)) fs in
                    Prims.not uu___3 in
                  if uu___2
                  then []
                  else
                    (let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = key dt.FStarC_Custard_Syntax.dt_name in
                           [uu___6] in
                         ctor_plan look uu___5 fs in
                       (cn, uu___4) in
                     [uu___3])) cs
     | uu___1 -> [])
let close_fields (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType dt ->
      let bound v =
        FStarC_List.existsb (fun p -> p = v)
          dt.FStarC_Custard_Syntax.dt_params in
      let rec close c =
        match c with
        | FStarC_Custard_Syntax.TVar v ->
            let uu___ = bound v in
            if uu___ then c else FStarC_Custard_Syntax.TAny
        | FStarC_Custard_Syntax.TApp (n, args) ->
            let uu___ =
              let uu___1 = FStarC_List.map close args in (n, uu___1) in
            FStarC_Custard_Syntax.TApp uu___
        | FStarC_Custard_Syntax.TArrow (a, e, b) ->
            let uu___ =
              let uu___1 = close a in
              let uu___2 = close b in (uu___1, e, uu___2) in
            FStarC_Custard_Syntax.TArrow uu___
        | FStarC_Custard_Syntax.TTuple cs ->
            let uu___ = FStarC_List.map close cs in
            FStarC_Custard_Syntax.TTuple uu___
        | FStarC_Custard_Syntax.TBuf c1 ->
            let uu___ = close c1 in FStarC_Custard_Syntax.TBuf uu___
        | FStarC_Custard_Syntax.TRef c1 ->
            let uu___ = close c1 in FStarC_Custard_Syntax.TRef uu___
        | FStarC_Custard_Syntax.TInline c1 ->
            let uu___ = close c1 in FStarC_Custard_Syntax.TInline uu___
        | c1 -> c1 in
      let fields fs =
        FStarC_List.map
          (fun uu___ ->
             match uu___ with | (f, c) -> let uu___1 = close c in (f, uu___1))
          fs in
      let uu___ =
        let uu___1 =
          match dt.FStarC_Custard_Syntax.dt_body with
          | FStarC_Custard_Syntax.TAbbrev c ->
              let uu___2 = close c in FStarC_Custard_Syntax.TAbbrev uu___2
          | FStarC_Custard_Syntax.TRecord fs ->
              let uu___2 = fields fs in FStarC_Custard_Syntax.TRecord uu___2
          | FStarC_Custard_Syntax.TVariant cs ->
              let uu___2 =
                FStarC_List.map
                  (fun uu___3 ->
                     match uu___3 with
                     | (cn, fs) -> let uu___4 = fields fs in (cn, uu___4)) cs in
              FStarC_Custard_Syntax.TVariant uu___2
          | FStarC_Custard_Syntax.TAbstract ->
              FStarC_Custard_Syntax.TAbstract in
        {
          FStarC_Custard_Syntax.dt_name = (dt.FStarC_Custard_Syntax.dt_name);
          FStarC_Custard_Syntax.dt_params =
            (dt.FStarC_Custard_Syntax.dt_params);
          FStarC_Custard_Syntax.dt_body = uu___1;
          FStarC_Custard_Syntax.dt_flags =
            (dt.FStarC_Custard_Syntax.dt_flags)
        } in
      FStarC_Custard_Syntax.DType uu___
  | d1 -> d1
let run
  (imports :
    (FStarC_Custard_Syntax.dtype * FStarC_Custard_Syntax.type_info)
      Prims.list)
  (prog : FStarC_Custard_Syntax.program) :
  (FStarC_Custard_Syntax.program * (FStarC_Custard_Syntax.name *
    FStarC_Custard_Syntax.type_info) Prims.list *
    FStarC_Custard_Syntax.verdicts)=
  let prog1 = FStarC_List.map close_fields prog in
  let t =
    let uu___ = FStarC_SMap.create (Prims.of_int 100) in
    let uu___1 = FStarC_SMap.create (Prims.of_int 100) in
    let uu___2 = FStarC_SMap.create (Prims.of_int 100) in
    let uu___3 = FStarC_SMap.create (Prims.of_int 100) in
    let uu___4 = FStarC_SMap.create (Prims.of_int 10) in
    let uu___5 = FStarC_Effect.mk_ref Prims.int_zero in
    {
      types = uu___;
      erased = uu___1;
      layouts = uu___2;
      ctors = uu___3;
      pinned = uu___4;
      fresh = uu___5
    } in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType dt ->
           let uu___1 = key dt.FStarC_Custard_Syntax.dt_name in
           FStarC_SMap.add t.types uu___1 dt
       | uu___1 -> ()) prog1;
  FStarC_List.iter
    (fun uu___2 ->
       match uu___2 with
       | (dt, ti) ->
           let k = key dt.FStarC_Custard_Syntax.dt_name in
           (FStarC_SMap.add t.pinned k ();
            FStarC_SMap.add t.erased k ti.FStarC_Custard_Syntax.ti_erased;
            FStarC_SMap.add t.layouts k ti.FStarC_Custard_Syntax.ti_layout;
            FStarC_List.iter
              (fun cl ->
                 let uu___6 = key cl.FStarC_Custard_Syntax.cl_name in
                 FStarC_SMap.add t.ctors uu___6 (k, cl))
              ti.FStarC_Custard_Syntax.ti_ctors)) imports;
  FStarC_Custard_Prof.timed "l.erasure" (fun uu___3 -> erasure_fixpoint t);
  FStarC_Custard_Prof.timed "l.layouts" (fun uu___4 -> compute_layouts t);
  FStarC_Custard_Prof.timed "l.ctors" (fun uu___5 -> register_ctors t);
  (let prog2 =
     FStarC_Custard_Prof.timed "l.eta_ctors"
       (fun uu___5 -> eta_ctors t imports prog1) in
   (let uu___6 = FStarC_Options.custard_dump_layouts () in
    if uu___6
    then
      (FStarC_Format.print_string "Custard layouts:\n";
       FStarC_SMap.iter t.layouts
         (fun k l ->
            let uu___8 = layout_to_string l in
            FStarC_Format.print2 "  %s : %s\n" k uu___8))
    else ());
   (let prog' =
      FStarC_Custard_Prof.timed "l.rewrite"
        (fun uu___6 -> FStarC_List.collect (rw_decl t) prog2) in
    let final = FStarC_SMap.create (Prims.of_int 100) in
    FStarC_List.iter
      (fun uu___7 ->
         match uu___7 with
         | (dt, uu___8) ->
             let uu___9 = key dt.FStarC_Custard_Syntax.dt_name in
             FStarC_SMap.add final uu___9 dt) imports;
    FStarC_List.iter
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DType dt ->
             let uu___8 = key dt.FStarC_Custard_Syntax.dt_name in
             FStarC_SMap.add final uu___8 dt
         | uu___8 -> ()) prog';
    (let look n = let uu___8 = key n in FStarC_SMap.try_find final uu___8 in
     let vd =
       let uu___8 = FStarC_SMap.create (Prims.of_int 50) in
       let uu___9 = FStarC_SMap.create (Prims.of_int 50) in
       {
         FStarC_Custard_Syntax.vd_records = uu___8;
         FStarC_Custard_Syntax.vd_plans = uu___9
       } in
     FStarC_List.iter
       (fun uu___9 ->
          match uu___9 with
          | (dt, ti) ->
              (if ti.FStarC_Custard_Syntax.ti_record
               then
                 (match ((dt.FStarC_Custard_Syntax.dt_body),
                          (ti.FStarC_Custard_Syntax.ti_ctors))
                  with
                  | (FStarC_Custard_Syntax.TRecord uu___11, cl::[]) ->
                      let uu___12 = key cl.FStarC_Custard_Syntax.cl_name in
                      FStarC_SMap.add vd.FStarC_Custard_Syntax.vd_records
                        uu___12 dt.FStarC_Custard_Syntax.dt_name
                  | (FStarC_Custard_Syntax.TVariant ((cn, uu___11)::[]),
                     uu___12) ->
                      let uu___13 = key cn in
                      FStarC_SMap.add vd.FStarC_Custard_Syntax.vd_records
                        uu___13 dt.FStarC_Custard_Syntax.dt_name
                  | uu___11 -> ())
               else ();
               FStarC_List.iter
                 (fun uu___11 ->
                    match uu___11 with
                    | (cn, pl) ->
                        let uu___12 = key cn in
                        FStarC_SMap.add vd.FStarC_Custard_Syntax.vd_plans
                          uu___12 pl) ti.FStarC_Custard_Syntax.ti_plans))
       imports;
     (let derived = FStarC_SMap.create (Prims.of_int 50) in
      FStarC_List.iter
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DType dt when
               let uu___10 =
                 let uu___11 = key dt.FStarC_Custard_Syntax.dt_name in
                 FStarC_SMap.try_find t.pinned uu___11 in
               match uu___10 with
               | FStar_Pervasives_Native.None -> true
               | uu___11 -> false ->
               let is_rec = record_verdict dt in
               let plans = ctor_plans look dt in
               ((let uu___11 = key dt.FStarC_Custard_Syntax.dt_name in
                 FStarC_SMap.add derived uu___11 (is_rec, plans));
                (match dt.FStarC_Custard_Syntax.dt_body with
                 | FStarC_Custard_Syntax.TVariant ((cn, uu___12)::[]) when
                     is_rec ->
                     let uu___13 = key cn in
                     FStarC_SMap.add vd.FStarC_Custard_Syntax.vd_records
                       uu___13 dt.FStarC_Custard_Syntax.dt_name
                 | uu___12 -> ());
                FStarC_List.iter
                  (fun uu___12 ->
                     match uu___12 with
                     | (cn, pl) ->
                         let uu___13 = key cn in
                         FStarC_SMap.add vd.FStarC_Custard_Syntax.vd_plans
                           uu___13 pl) plans)
           | uu___10 -> ()) prog';
      (let infos =
         let uu___10 = FStarC_SMap.keys t.types in
         FStarC_List.collect
           (fun k ->
              let uu___11 =
                let uu___12 = FStarC_SMap.try_find t.pinned k in
                match uu___12 with
                | FStar_Pervasives_Native.Some v -> true
                | uu___13 -> false in
              if uu___11
              then []
              else
                (let uu___12 =
                   let uu___13 = FStarC_SMap.try_find t.types k in
                   let uu___14 = FStarC_SMap.try_find t.layouts k in
                   (uu___13, uu___14) in
                 match uu___12 with
                 | (FStar_Pervasives_Native.Some d,
                    FStar_Pervasives_Native.Some l) ->
                     let uu___13 =
                       let uu___14 = FStarC_SMap.try_find derived k in
                       match uu___14 with
                       | FStar_Pervasives_Native.Some v -> v
                       | FStar_Pervasives_Native.None -> (false, []) in
                     (match uu___13 with
                      | (is_rec, plans) ->
                          let uu___14 =
                            let uu___15 =
                              let uu___16 =
                                let uu___17 = FStarC_SMap.try_find t.erased k in
                                match uu___17 with
                                | FStar_Pervasives_Native.Some b -> b
                                | FStar_Pervasives_Native.None -> false in
                              let uu___17 = ctor_layouts t d in
                              {
                                FStarC_Custard_Syntax.ti_erased = uu___16;
                                FStarC_Custard_Syntax.ti_layout = l;
                                FStarC_Custard_Syntax.ti_ctors = uu___17;
                                FStarC_Custard_Syntax.ti_record = is_rec;
                                FStarC_Custard_Syntax.ti_plans = plans
                              } in
                            ((d.FStarC_Custard_Syntax.dt_name), uu___15) in
                          [uu___14])
                 | uu___13 -> [])) uu___10 in
       (prog', infos, vd))))))
