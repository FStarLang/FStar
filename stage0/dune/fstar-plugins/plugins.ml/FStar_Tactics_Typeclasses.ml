open Fstarcompiler
open Prims
let op_At (uu___ : unit) :
  'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list=
  FStar_List_Tot_Base.op_At
let tc_norm_steps : Fstarcompiler.FStarC_NormSteps.norm_step Prims.list=
  [Fstarcompiler.FStarC_NormSteps.primops;
  Fstarcompiler.FStarC_NormSteps.iota;
  Fstarcompiler.FStarC_NormSteps.delta_qualifier ["unfold"]]
type glb_inst = {
  inst_name: FStarC_Reflection_Types.fv ;
  noinst: Prims.bool }
let __proj__Mkglb_inst__item__inst_name (projectee : glb_inst) :
  FStarC_Reflection_Types.fv=
  match projectee with | { inst_name; noinst;_} -> inst_name
let __proj__Mkglb_inst__item__noinst (projectee : glb_inst) : Prims.bool=
  match projectee with | { inst_name; noinst;_} -> noinst
type glb_entry =
  {
  class_name: FStarC_Reflection_Types.fv ;
  instances: glb_inst Prims.list }
let __proj__Mkglb_entry__item__class_name (projectee : glb_entry) :
  FStarC_Reflection_Types.fv=
  match projectee with | { class_name; instances;_} -> class_name
let __proj__Mkglb_entry__item__instances (projectee : glb_entry) :
  glb_inst Prims.list=
  match projectee with | { class_name; instances;_} -> instances
let unembed_int (uu___ : FStar_Tactics_NamedView.term) :
  (Prims.int FStar_Pervasives_Native.option, unit)
    FStar_Tactics_Effect.tac_repr=
  (fun t ->
     Obj.magic
       (fun uu___ ->
          match FStarC_Reflection_V2_Builtins.inspect_ln t with
          | FStarC_Reflection_V2_Data.Tv_Const
              (FStarC_Reflection_V2_Data.C_Int i) ->
              FStar_Pervasives_Native.Some i
          | uu___1 -> FStar_Pervasives_Native.None)) uu___
let rec unembed_list :
  'a .
    (FStar_Tactics_NamedView.term ->
       ('a FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      FStar_Tactics_NamedView.term ->
        ('a Prims.list FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun u t ps ->
    let x = FStar_Tactics_V2_SyntaxHelpers.hua t ps in
    match x with
    | FStar_Pervasives_Native.Some
        (fv, uu___,
         (ty, FStarC_Reflection_V2_Data.Q_Implicit)::(hd,
                                                      FStarC_Reflection_V2_Data.Q_Explicit)::
         (tl, FStarC_Reflection_V2_Data.Q_Explicit)::[])
        ->
        if
          (FStarC_Reflection_V2_Builtins.implode_qn
             (FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = "Prims.Cons"
        then
          let x1 =
            let x2 = u hd ps in let x3 = unembed_list u tl ps in (x2, x3) in
          (match x1 with
           | (FStar_Pervasives_Native.Some hd1, FStar_Pervasives_Native.Some
              tl1) -> FStar_Pervasives_Native.Some (hd1 :: tl1)
           | uu___1 -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some
        (fv, uu___, (ty, FStarC_Reflection_V2_Data.Q_Implicit)::[]) ->
        if
          (FStarC_Reflection_V2_Builtins.implode_qn
             (FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = "Prims.Nil"
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let extract_fundeps (se : FStarC_Reflection_Types.sigelt) :
  (Prims.int Prims.list FStar_Pervasives_Native.option, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Reflection_V2_Builtins.sigelt_attrs se in
    match x with
    | [] -> FStar_Pervasives_Native.None
    | attr::attrs' ->
        FStar_Tactics_Effect.tac_bind
          (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.collect_app attr))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (hd, (a0, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
                    if
                      FStar_Reflection_TermEq_Simple.term_eq hd
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "Typeclasses";
                                 "fundeps"])))
                    then Obj.magic (unembed_list unembed_int a0)
                    else
                      (let rec aux uu___2 =
                         (fun attrs ->
                            match attrs with
                            | [] ->
                                Obj.magic
                                  (Obj.repr
                                     (fun uu___2 ->
                                        FStar_Pervasives_Native.None))
                            | attr1::attrs'1 ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (Obj.magic
                                           (FStar_Tactics_V2_SyntaxHelpers.collect_app
                                              attr1))
                                        (fun uu___2 ->
                                           (fun uu___2 ->
                                              match uu___2 with
                                              | (hd1,
                                                 (a01,
                                                  FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                                  ->
                                                  if
                                                    FStar_Reflection_TermEq_Simple.term_eq
                                                      hd1
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "Typeclasses";
                                                               "fundeps"])))
                                                  then
                                                    Obj.magic
                                                      (unembed_list
                                                         unembed_int a01)
                                                  else
                                                    Obj.magic (aux attrs'1)
                                              | uu___3 ->
                                                  Obj.magic (aux attrs'1))
                                             uu___2)))) uu___2 in
                       Obj.magic (aux attrs'))
                | uu___1 ->
                    let rec aux uu___2 =
                      (fun attrs ->
                         match attrs with
                         | [] ->
                             Obj.magic
                               (Obj.repr
                                  (fun uu___2 -> FStar_Pervasives_Native.None))
                         | attr1::attrs'1 ->
                             Obj.magic
                               (Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (Obj.magic
                                        (FStar_Tactics_V2_SyntaxHelpers.collect_app
                                           attr1))
                                     (fun uu___2 ->
                                        (fun uu___2 ->
                                           match uu___2 with
                                           | (hd,
                                              (a0,
                                               FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                               ->
                                               if
                                                 FStar_Reflection_TermEq_Simple.term_eq
                                                   hd
                                                   (FStarC_Reflection_V2_Builtins.pack_ln
                                                      (FStarC_Reflection_V2_Data.Tv_FVar
                                                         (FStarC_Reflection_V2_Builtins.pack_fv
                                                            ["FStar";
                                                            "Tactics";
                                                            "Typeclasses";
                                                            "fundeps"])))
                                               then
                                                 Obj.magic
                                                   (unembed_list unembed_int
                                                      a0)
                                               else Obj.magic (aux attrs'1)
                                           | uu___3 ->
                                               Obj.magic (aux attrs'1))
                                          uu___2)))) uu___2 in
                    Obj.magic (aux attrs')) uu___) ps
let sigelt_name (uu___ : FStarC_Reflection_Types.sigelt) :
  (FStarC_Reflection_Types.fv, unit) FStar_Tactics_Effect.tac_repr=
  (fun se ->
     match FStarC_Reflection_V2_Builtins.inspect_sigelt se with
     | FStarC_Reflection_V2_Data.Sg_Let (uu___, lbs) ->
         Obj.magic
           (Obj.repr
              (match lbs with
               | lb::[] ->
                   Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           (FStarC_Reflection_V2_Builtins.inspect_lb lb).FStarC_Reflection_V2_Data.lb_fv))
               | uu___1 -> Obj.repr (FStar_Tactics_V2_Derived.fail "GGG1")))
     | FStarC_Reflection_V2_Data.Sg_Val (nm, uu___, uu___1) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 -> FStarC_Reflection_V2_Builtins.pack_fv nm)))
     | uu___ -> Obj.magic (Obj.repr (FStar_Tactics_V2_Derived.fail "GGG2")))
    uu___
let rec head_of (t : FStar_Tactics_NamedView.term) :
  (FStarC_Reflection_Types.fv FStar_Pervasives_Native.option, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_FVar fv -> FStar_Pervasives_Native.Some fv
    | FStar_Tactics_NamedView.Tv_UInst (fv, uu___) ->
        FStar_Pervasives_Native.Some fv
    | FStar_Tactics_NamedView.Tv_App (h, uu___) -> head_of h ps
    | v -> FStar_Pervasives_Native.None
let rec res_typ (t : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_NamedView.inspect t ps in
    match x with
    | FStar_Tactics_NamedView.Tv_Arrow (uu___, c) ->
        (match FStar_Tactics_NamedView.inspect_comp c with
         | FStarC_Reflection_V2_Data.C_Total t1 -> res_typ t1 ps
         | uu___1 -> t)
    | uu___ -> t
let fv_eq (fv1 : FStarC_Reflection_Types.fv)
  (fv2 : FStarC_Reflection_Types.fv) : Prims.bool=
  let n1 = FStarC_Reflection_V2_Builtins.inspect_fv fv1 in
  let n2 = FStarC_Reflection_V2_Builtins.inspect_fv fv2 in n1 = n2
let rec compact (uu___ : glb_entry Prims.list) :
  (glb_entry Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  (fun xs ->
     match xs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> []))
     | x::xs1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_List_Tot_Base.partition
                         (fun y -> fv_eq x.class_name y.class_name) xs1))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | (same, rest) ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Obj.magic (compact rest))
                                (fun uu___1 uu___2 ->
                                   {
                                     class_name = (x.class_name);
                                     instances =
                                       ((op_At ()) x.instances
                                          (FStar_List_Tot_Base.concatMap
                                             (fun y -> y.instances) same))
                                   } :: uu___1))) uu___)))) uu___
let is_class_name (f : FStarC_Reflection_Types.fv) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStar_Tactics_V2_Derived.cur_env () ps in
      FStarC_Reflection_V2_Builtins.lookup_typ x1
        (FStarC_Reflection_V2_Builtins.inspect_fv f) in
    match x with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some se ->
        FStar_List_Tot_Base.existsb
          (FStar_Reflection_TermEq_Simple.term_eq
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Typeclasses"; "tcclass"]))))
          (FStarC_Reflection_V2_Builtins.sigelt_attrs se)
let class_of_typ (t : FStar_Tactics_NamedView.term) :
  (FStarC_Reflection_Types.fv FStar_Pervasives_Native.option, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = let x1 = res_typ t ps in head_of x1 ps in
    match x with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some fv ->
        let x1 = is_class_name fv ps in
        if x1
        then FStar_Pervasives_Native.Some fv
        else
          (let x2 =
             FStar_Tactics_V2_Derived.try_with
               (fun uu___1 ->
                  match () with
                  | () ->
                      FStar_Tactics_V2_Derived.norm_term
                        (Fstarcompiler.FStarC_NormSteps.hnf :: tc_norm_steps)
                        t)
               (fun uu___1 ->
                  (fun uu___1 -> Obj.magic (fun uu___2 -> t)) uu___1) ps in
           let x3 = res_typ x2 ps in head_of x3 ps)
let type_matches_class (cfv : FStarC_Reflection_Types.fv)
  (t : FStar_Tactics_NamedView.term) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = class_of_typ t ps in
    match x with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some fv -> fv_eq cfv fv
let build_glb_map (all_glb : FStarC_Reflection_Types.sigelt Prims.list) :
  (glb_entry Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x se ps1 =
      let x1 = sigelt_name se ps1 in
      {
        inst_name = x1;
        noinst =
          (FStar_List_Tot_Base.existsb
             (FStar_Reflection_TermEq_Simple.term_eq
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar"; "Tactics"; "Typeclasses"; "noinst"]))))
             (FStarC_Reflection_V2_Builtins.sigelt_attrs se))
      } in
    let x1 =
      FStar_Tactics_Util.concatMap
        (fun se ps1 ->
           let x2 = x se ps1 in
           let x3 =
             FStar_Tactics_V2_Derived.try_with
               (fun uu___ ->
                  match () with
                  | () ->
                      (fun ps2 ->
                         let x4 =
                           let x5 = FStar_Tactics_V2_Derived.cur_env () ps2 in
                           FStarC_Tactics_V2_Builtins.tc x5
                             (FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_FVar
                                   (x2.inst_name))) ps2 in
                         FStar_Pervasives_Native.Some x4))
               (fun uu___ ->
                  (fun uu___ ->
                     Obj.magic (fun uu___1 -> FStar_Pervasives_Native.None))
                    uu___) ps1 in
           match x3 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some typ ->
               let x4 = FStarC_Reflection_V2_Builtins.sigelt_attrs se in
               let x5 = class_of_typ typ ps1 in
               (match x5 with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some cvf ->
                    [{ class_name = cvf; instances = [x2] }])) all_glb ps in
    compact x1 ps
type st_t =
  {
  seen: FStar_Tactics_NamedView.term Prims.list ;
  glb: glb_entry Prims.list ;
  fuel: Prims.int ;
  rng: FStar_Range.range ;
  warned_oof: Prims.bool FStarC_Tactics_Types.tref ;
  dbg: Prims.bool }
let __proj__Mkst_t__item__seen (projectee : st_t) :
  FStar_Tactics_NamedView.term Prims.list=
  match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> seen
let __proj__Mkst_t__item__glb (projectee : st_t) : glb_entry Prims.list=
  match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> glb
let __proj__Mkst_t__item__fuel (projectee : st_t) : Prims.int=
  match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> fuel
let __proj__Mkst_t__item__rng (projectee : st_t) : FStar_Range.range=
  match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> rng
let __proj__Mkst_t__item__warned_oof (projectee : st_t) :
  Prims.bool FStarC_Tactics_Types.tref=
  match projectee with
  | { seen; glb; fuel; rng; warned_oof; dbg;_} -> warned_oof
let __proj__Mkst_t__item__dbg (projectee : st_t) : Prims.bool=
  match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> dbg
let debug (uu___1 : st_t)
  (uu___ : unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun st f ->
     if st.dbg
     then
       Obj.magic
         (Obj.repr
            (fun ps ->
               let x = f () ps in FStarC_Tactics_V2_Builtins.print x ps))
     else
       Obj.magic
         (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
    uu___1 uu___
type tc_goal =
  {
  g: FStar_Tactics_NamedView.term ;
  head_fv: FStarC_Reflection_Types.fv ;
  c_se: FStarC_Reflection_Types.sigelt FStar_Pervasives_Native.option ;
  fundeps: Prims.int Prims.list FStar_Pervasives_Native.option ;
  args_and_uvars: (FStarC_Reflection_V2_Data.argv * Prims.bool) Prims.list }
let __proj__Mktc_goal__item__g (projectee : tc_goal) :
  FStar_Tactics_NamedView.term=
  match projectee with | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> g
let __proj__Mktc_goal__item__head_fv (projectee : tc_goal) :
  FStarC_Reflection_Types.fv=
  match projectee with
  | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> head_fv
let __proj__Mktc_goal__item__c_se (projectee : tc_goal) :
  FStarC_Reflection_Types.sigelt FStar_Pervasives_Native.option=
  match projectee with
  | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> c_se
let __proj__Mktc_goal__item__fundeps (projectee : tc_goal) :
  Prims.int Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> fundeps
let __proj__Mktc_goal__item__args_and_uvars (projectee : tc_goal) :
  (FStarC_Reflection_V2_Data.argv * Prims.bool) Prims.list=
  match projectee with
  | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> args_and_uvars
exception Next 
let uu___is_Next (projectee : Prims.exn) : Prims.bool=
  match projectee with | Next -> true | uu___ -> false
let skip (st : st_t) (s : Prims.string) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    if st.dbg
    then FStarC_Tactics_V2_Builtins.print (Prims.strcat "skip: " s) ps
    else ();
    Obj.magic (FStarC_Tactics_V2_Builtins.raise_core Next ps)
let orskip (st : st_t) (s : Prims.string)
  (k : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.try_with (fun uu___ -> match () with | () -> k ())
    (fun uu___ -> skip st s)
let op_Greater_Greater_Greater
  (t1 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (t2 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.try_with
    (fun uu___1 -> match () with | () -> t1 ())
    (fun uu___1 ->
       match uu___1 with
       | Next -> t2 ()
       | e ->
           FStar_Tactics_Effect.tac_bind
             (Obj.magic (FStarC_Tactics_V2_Builtins.raise_core e))
             (fun uu___2 uu___3 -> Obj.magic ()))
let run (t : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr= t ()
let rec first :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f l ->
    match l with
    | [] ->
        (fun ps -> Obj.magic (FStarC_Tactics_V2_Builtins.raise_core Next ps))
    | x::xs ->
        run
          (op_Greater_Greater_Greater (fun uu___ -> f x)
             (fun uu___ -> first f xs))
let rec maybe_intros (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_Derived.cur_goal () ps in
    let x1 = FStar_Tactics_NamedView.inspect x ps in
    match x1 with
    | FStar_Tactics_NamedView.Tv_Arrow (uu___1, uu___2) ->
        ((let x3 = FStarC_Tactics_V2_Builtins.intro () ps in ());
         maybe_intros () ps)
    | uu___1 -> ()
let trywith (st : st_t) (g : tc_goal) (t : FStar_Tactics_NamedView.term)
  (noinst : Prims.bool)
  (k : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 =
        FStar_Tactics_Util.mapi
          (fun uu___1 uu___ ->
             (fun i uu___ ->
                Obj.magic
                  (fun uu___1 ->
                     match uu___ with | (uu___2, b) -> if b then [i] else []))
               uu___1 uu___) g.args_and_uvars ps in
      FStar_List_Tot_Base.flatten x1 in
    debug st
      (fun uu___ ps1 ->
         let x2 = FStarC_Tactics_V2_Builtins.term_to_string t ps1 in
         Prims.strcat "Trying to apply hypothesis/instance: " x2) ps;
    FStar_Tactics_V2_Derived.seq
      (fun uu___ ->
         if noinst
         then
           orskip st "apply_noinst"
             (fun uu___1 -> FStar_Tactics_V2_Derived.apply_noinst t)
         else
           if Prims.uu___is_Cons x
           then
             FStar_Tactics_Effect.tac_bind
               (if FStar_Pervasives_Native.uu___is_None g.fundeps
                then
                  Obj.magic
                    (Obj.repr
                       (skip st
                          "Will not continue as there are unresolved args (and no fundeps)"))
                else
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
               (fun uu___2 ->
                  (fun uu___2 ->
                     Obj.magic
                       (fun ps1 ->
                          let x2 = g.fundeps in
                          match x2 with
                          | FStar_Pervasives_Native.Some fundeps ->
                              (debug st
                                 (fun uu___3 ->
                                    (fun uu___3 ->
                                       Obj.magic
                                         (fun uu___4 -> "checking fundeps"))
                                      uu___3) ps1;
                               if
                                 FStar_List_Tot_Base.existsb
                                   (fun i ->
                                      Prims.op_Negation
                                        (FStar_List_Tot_Base.mem i fundeps))
                                   x
                               then
                                 skip st
                                   "fundeps: a non-fundep is unresolved" ps1
                               else ();
                               orskip st "apply"
                                 (fun uu___3 ->
                                    FStar_Tactics_V2_Derived.apply t) ps1)))
                    uu___2)
           else
             orskip st "apply_noinst"
               (fun uu___3 -> FStar_Tactics_V2_Derived.apply_noinst t))
      (fun uu___ ps1 ->
         debug st
           (fun uu___1 ps2 ->
              FStarC_Tactics_V2_Builtins.dump "next" ps2;
              (let x4 =
                 let x5 = FStarC_Tactics_V2_Builtins.term_to_string t ps2 in
                 Prims.strcat x5 " seems to have worked" in
               Prims.strcat "apply of " x4)) ps1;
         (let x3 =
            {
              seen = (st.seen);
              glb = (st.glb);
              fuel = (st.fuel - Prims.int_one);
              rng = (st.rng);
              warned_oof = (st.warned_oof);
              dbg = (st.dbg)
            } in
          k x3 ps1)) ps
let local (st : st_t) (g : tc_goal)
  (k : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    debug st
      (fun uu___1 ps1 ->
         let x1 = FStarC_Tactics_V2_Builtins.term_to_string g.g ps1 in
         Prims.strcat "local, goal = " x1) ps;
    (let x1 =
       let x2 = FStar_Tactics_V2_Derived.cur_env () ps in
       FStarC_Reflection_V2_Builtins.vars_of_env x2 in
     first
       (fun b ps1 ->
          let x2 =
            type_matches_class g.head_fv b.FStarC_Reflection_V2_Data.sort3
              ps1 in
          if x2
          then
            trywith st g
              (FStar_Tactics_NamedView.pack
                 (FStar_Tactics_NamedView.Tv_Var
                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv b)))
              false k ps1
          else skip st "head mismatch" ps1) x1 ps)
let global (st : st_t) (g : tc_goal)
  (k : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    debug st
      (fun uu___1 ps1 ->
         let x1 = FStarC_Tactics_V2_Builtins.term_to_string g.g ps1 in
         Prims.strcat "global, goal = " x1) ps;
    (match st.glb with
     | [] -> skip st "no more global instances" ps
     | { class_name; instances;_}::rest ->
         FStar_Tactics_Effect.tac_bind
           (Obj.magic
              (type_matches_class g.head_fv
                 (FStar_Tactics_NamedView.pack
                    (FStar_Tactics_NamedView.Tv_FVar class_name))))
           (fun uu___1 ->
              (fun uu___1 ->
                 if uu___1
                 then
                   Obj.magic
                     (first
                        (fun i ->
                           trywith st g
                             (FStar_Tactics_NamedView.pack
                                (FStar_Tactics_NamedView.Tv_FVar
                                   (i.inst_name))) i.noinst k) instances)
                 else
                   (let rec go l =
                      match l with
                      | [] -> skip st "no more global instances"
                      | { class_name = class_name1; instances = instances1;_}::rest1
                          ->
                          FStar_Tactics_Effect.tac_bind
                            (Obj.magic
                               (type_matches_class g.head_fv
                                  (FStar_Tactics_NamedView.pack
                                     (FStar_Tactics_NamedView.Tv_FVar
                                        class_name1))))
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  if uu___3
                                  then
                                    Obj.magic
                                      (first
                                         (fun i ->
                                            trywith st g
                                              (FStar_Tactics_NamedView.pack
                                                 (FStar_Tactics_NamedView.Tv_FVar
                                                    (i.inst_name))) i.noinst
                                              k) instances1)
                                  else Obj.magic (go rest1)) uu___3) in
                    Obj.magic (go rest))) uu___1) ps)
let rec unrefine (uu___ : FStar_Tactics_NamedView.named_term_view) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun t ->
     match t with
     | FStar_Tactics_NamedView.Tv_Refine (b, t1) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_NamedView.inspect
                       b.FStar_Tactics_NamedView.sort))
                 (fun uu___ ->
                    (fun uu___ -> Obj.magic (unrefine uu___)) uu___)))
     | FStar_Tactics_NamedView.Tv_AscribedT (e, uu___, uu___1, uu___2) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStar_Tactics_NamedView.inspect e))
                 (fun uu___3 ->
                    (fun uu___3 -> Obj.magic (unrefine uu___3)) uu___3)))
     | FStar_Tactics_NamedView.Tv_AscribedC (e, uu___, uu___1, uu___2) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStar_Tactics_NamedView.inspect e))
                 (fun uu___3 ->
                    (fun uu___3 -> Obj.magic (unrefine uu___3)) uu___3)))
     | uu___ ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> FStar_Tactics_NamedView.pack t)))) uu___
let try_trivial (g : FStar_Tactics_NamedView.term)
  (k : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 =
        let x2 = FStar_Tactics_NamedView.inspect g ps in unrefine x2 ps in
      FStar_Tactics_V2_SyntaxHelpers.hua x1 ps in
    match x with
    | FStar_Pervasives_Native.Some (fv, u, a) ->
        if
          (FStarC_Reflection_V2_Builtins.implode_qn
             (FStarC_Reflection_V2_Builtins.inspect_fv fv))
            = "Prims.unit"
        then
          FStar_Tactics_V2_Derived.exact
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_Const
                  FStarC_Reflection_V2_Data.C_Unit)) ps
        else
          if
            (FStarC_Reflection_V2_Builtins.implode_qn
               (FStarC_Reflection_V2_Builtins.inspect_fv fv))
              = "Prims.squash"
          then FStar_Tactics_V2_Derived.smt () ps
          else FStarC_Tactics_V2_Builtins.raise_core Next ps
    | uu___1 -> FStarC_Tactics_V2_Builtins.raise_core Next ps
let rec tac_unrefine (uu___ : unit) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_Derived.cur_goal () ps in
    match FStarC_Reflection_V2_Builtins.inspect_ln x with
    | FStarC_Reflection_V2_Data.Tv_Refine (b, ref) ->
        let x1 =
          (FStarC_Reflection_V2_Builtins.inspect_binder b).FStarC_Reflection_V2_Data.sort2 in
        let x2 =
          FStar_Tactics_V2_Derived.fresh_uvar
            (FStar_Pervasives_Native.Some x1) ps in
        (FStar_Tactics_V2_Derived.exact_with_ref x2 ps;
         FStarC_Tactics_V2_Builtins.unshelve x2 ps;
         (let x6 = tac_unrefine () ps in ());
         true)
    | uu___1 -> false
let try_unrefining (st : st_t)
  (k : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = tac_unrefine () ps in
    if x then k st ps else FStarC_Tactics_V2_Builtins.raise_core Next ps
let try_instances (st : st_t)
  (k : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_Derived.cur_goal () ps in
    let x1 = FStar_Tactics_V2_SyntaxHelpers.hua x ps in
    match x1 with
    | FStar_Pervasives_Native.None ->
        (debug st
           (fun uu___1 ps1 ->
              let x3 = FStarC_Tactics_V2_Builtins.term_to_string x ps1 in
              Prims.strcat "Goal does not look like a typeclass: " x3) ps;
         FStarC_Tactics_V2_Builtins.raise_core Next ps)
    | FStar_Pervasives_Native.Some (head_fv, us, args) ->
        let x2 =
          let x3 = FStar_Tactics_V2_Derived.cur_env () ps in
          FStarC_Reflection_V2_Builtins.lookup_typ x3
            (FStarC_Reflection_V2_Builtins.inspect_fv head_fv) in
        let x3 =
          match x2 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some se -> extract_fundeps se ps in
        let x4 =
          FStar_Tactics_Util.map
            (fun uu___1 ->
               match uu___1 with
               | (a, q) ->
                   FStar_Tactics_Effect.tac_bind
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (Obj.magic
                              (FStarC_Tactics_V2_Builtins.free_uvars a))
                           (fun uu___2 uu___3 -> Prims.uu___is_Cons uu___2)))
                     (fun uu___2 uu___3 -> ((a, q), uu___2))) args ps in
        let x5 =
          {
            seen = (x :: (st.seen));
            glb = (st.glb);
            fuel = (st.fuel);
            rng = (st.rng);
            warned_oof = (st.warned_oof);
            dbg = (st.dbg)
          } in
        let x6 =
          { g = x; head_fv; c_se = x2; fundeps = x3; args_and_uvars = x4 } in
        run (op_Greater_Greater_Greater (local x5 x6 k) (global x5 x6 k)) ps
let rec tcresolve' (st : st_t) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    if st.fuel <= Prims.int_zero
    then
      (let x1 = st.warned_oof in
       (let x3 =
          let x4 = FStarC_Tactics_V2_Builtins.read x1 ps in
          Prims.op_Negation x4 in
        if x3
        then
          (FStarC_Tactics_V2_Builtins.log_issues
             [FStar_Issue.mk_issue_doc "Warning"
                [FStar_Pprint.arbitrary_string
                   "Warning: fuel exhausted during typeclass resolution.";
                FStar_Pprint.arbitrary_string
                  "This usually indicates a loop in your instances."]
                (FStar_Pervasives_Native.Some (st.rng))
                FStar_Pervasives_Native.None []] ps;
           FStarC_Tactics_V2_Builtins.write x1 true ps)
        else ());
       FStarC_Tactics_V2_Builtins.raise_core Next ps)
    else ();
    debug st
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (fun uu___1 ->
                 Prims.strcat "fuel = " (Prims.string_of_int st.fuel))) uu___)
      ps;
    FStarC_Tactics_V2_Builtins.norm tc_norm_steps ps;
    maybe_intros () ps;
    (let x4 = FStar_Tactics_V2_Derived.cur_goal () ps in
     if
       FStar_List_Tot_Base.existsb
         (FStar_Reflection_TermEq_Simple.term_eq x4) st.seen
     then
       (debug st
          (fun uu___ -> (fun uu___ -> Obj.magic (fun uu___1 -> "loop")) uu___)
          ps;
        FStarC_Tactics_V2_Builtins.raise_core Next ps)
     else ();
     run
       (op_Greater_Greater_Greater
          (op_Greater_Greater_Greater (try_trivial x4 tcresolve')
             (try_instances st tcresolve')) (try_unrefining st tcresolve'))
       ps)
let __tcresolve (dbg : Prims.bool) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    if dbg
    then FStarC_Tactics_V2_Builtins.dump "tcresolve entry point" ps
    else ();
    (let x1 = FStar_Tactics_V2_Derived.cur_witness () ps in
     FStarC_Tactics_V2_Builtins.set_dump_on_failure false ps;
     maybe_intros () ps;
     (let x4 =
        let x5 = FStar_Tactics_V2_Derived.cur_env () ps in
        FStarC_Reflection_V2_Builtins.lookup_attr_ses
          (FStarC_Reflection_V2_Builtins.pack_ln
             (FStarC_Reflection_V2_Data.Tv_FVar
                (FStarC_Reflection_V2_Builtins.pack_fv
                   ["FStar"; "Tactics"; "Typeclasses"; "tcinstance"]))) x5 in
      let x5 = build_glb_map x4 ps in
      let x6 =
        let x7 =
          let x8 = FStar_Tactics_V2_Derived.cur_goal () ps in
          FStarC_Reflection_V2_Builtins.range_of_term x8 in
        let x8 = FStarC_Tactics_V2_Builtins.alloc false ps in
        {
          seen = [];
          glb = x5;
          fuel = (Prims.of_int (16));
          rng = x7;
          warned_oof = x8;
          dbg
        } in
      FStar_Tactics_V2_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               (fun ps1 ->
                  tcresolve' x6 ps1;
                  debug x6
                    (fun uu___1 ps2 ->
                       let x8 =
                         FStarC_Tactics_V2_Builtins.term_to_string x1 ps2 in
                       Prims.strcat "Solved to:\n\t" x8) ps1))
        (fun uu___ ->
           match uu___ with
           | Next ->
               (fun ps1 ->
                  let x7 =
                    let x8 =
                      let x9 =
                        let x10 =
                          let x11 = FStar_Tactics_V2_Derived.cur_goal () ps1 in
                          FStarC_Tactics_V2_Builtins.term_to_doc x11 ps1 in
                        FStar_Pprint.bquotes x10 in
                      FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                        (FStar_Pprint.arbitrary_string
                           "Could not solve typeclass constraint") x9 in
                    [x8] in
                  FStar_Tactics_V2_Derived.fail_doc x7 ps1)
           | FStarC_Tactics_Common.TacticFailure (msg, r) ->
               FStar_Tactics_V2_Derived.fail_doc_at
                 ((op_At ())
                    [FStar_Pprint.arbitrary_string
                       "Typeclass resolution failed."] msg) r
           | e ->
               FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStarC_Tactics_V2_Builtins.raise_core e))
                 (fun uu___1 uu___2 -> ())) ps))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.__tcresolve" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.__tcresolve (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 __tcresolve)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let tcresolve (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.debugging () ps in __tcresolve x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.tcresolve" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.tcresolve (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 tcresolve)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let tcresolve_debug (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr= __tcresolve true
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.tcresolve_debug" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.tcresolve_debug (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  tcresolve_debug)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec mk_abs (uu___1 : FStar_Tactics_NamedView.binder Prims.list)
  (uu___ : FStar_Tactics_NamedView.term) :
  (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun bs body ->
     match bs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> body))
     | b::bs1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic (mk_abs bs1 body))
                       (fun uu___ uu___1 ->
                          FStar_Tactics_NamedView.Tv_Abs (b, uu___))))
                 (fun uu___ uu___1 -> FStar_Tactics_NamedView.pack uu___))))
    uu___1 uu___
let rec last : 'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun l ->
       match l with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_V2_Derived.fail "last: empty list"))
       | x::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
       | uu___::xs -> Obj.magic (Obj.repr (last xs))) uu___
let filter_no_method_binders (bs : FStar_Tactics_NamedView.binders) :
  (FStar_Tactics_NamedView.binders, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x b =
      FStar_List_Tot_Base.existsb
        (FStar_Reflection_TermEq_Simple.term_eq
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Typeclasses"; "no_method"]))))
        b.FStar_Tactics_NamedView.attrs in
    FStar_Tactics_Util.filter
      (fun b ps1 ->
         let x1 =
           FStarC_Tactics_Unseal.unseal b.FStar_Tactics_NamedView.ppname ps1 in
         if (FStar_String.index x1 Prims.int_zero) = 95
         then false
         else Prims.op_Negation (x b)) bs ps
let binder_set_meta (b : FStar_Tactics_NamedView.binder)
  (t : FStar_Tactics_NamedView.term) : FStar_Tactics_NamedView.binder=
  {
    FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
    FStar_Tactics_NamedView.ppname = (b.FStar_Tactics_NamedView.ppname);
    FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
    FStar_Tactics_NamedView.qual = (FStarC_Reflection_V2_Data.Q_Meta t);
    FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
  }
let debug' (f : unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.debugging () ps in
    if x
    then let x1 = f () ps in FStarC_Tactics_V2_Builtins.print x1 ps
    else ()
let mk_class (nm : Prims.string) :
  (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Reflection_V2_Builtins.explode_qn nm in
    let x1 =
      let x2 = FStarC_Tactics_V2_Builtins.top_env () ps in
      FStarC_Reflection_V2_Builtins.lookup_typ x2 x in
    FStar_Tactics_V2_Derived.guard (FStar_Pervasives_Native.uu___is_Some x1)
      ps;
    (let x3 = x1 in
     match x3 with
     | FStar_Pervasives_Native.Some se ->
         let x4 =
           FStar_List_Tot_Base.filter
             (fun uu___ ->
                match uu___ with
                | FStarC_Reflection_V2_Data.Inline_for_extraction -> true
                | FStarC_Reflection_V2_Data.NoExtract -> true
                | uu___1 -> false)
             (FStarC_Reflection_V2_Builtins.sigelt_quals se) in
         let x5 = FStar_Tactics_NamedView.inspect_sigelt se ps in
         (FStar_Tactics_V2_Derived.guard
            (FStar_Tactics_NamedView.uu___is_Sg_Inductive x5) ps;
          (let x7 = x5 in
           match x7 with
           | FStar_Tactics_NamedView.Sg_Inductive
               { FStar_Tactics_NamedView.nm = name;
                 FStar_Tactics_NamedView.univs1 = us;
                 FStar_Tactics_NamedView.params = params;
                 FStar_Tactics_NamedView.typ = ity;
                 FStar_Tactics_NamedView.ctors = ctors;_}
               ->
               (debug'
                  (fun uu___ ps1 ->
                     let x9 =
                       FStar_Tactics_Util.string_of_list
                         FStar_Tactics_V2_Derived.binder_to_string params ps1 in
                     Prims.strcat "params = " x9) ps;
                debug'
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (fun uu___1 ->
                             Prims.strcat "got it, name = "
                               (FStarC_Reflection_V2_Builtins.implode_qn name)))
                       uu___) ps;
                debug'
                  (fun uu___ ps1 ->
                     let x11 =
                       FStarC_Tactics_V2_Builtins.term_to_string ity ps1 in
                     Prims.strcat "got it, ity = " x11) ps;
                (let x11 = last name ps in
                 FStar_Tactics_V2_Derived.guard
                   ((FStar_List_Tot_Base.length ctors) = Prims.int_one) ps;
                 (let x13 = ctors in
                  match x13 with
                  | (c_name, ty)::[] ->
                      (debug'
                         (fun uu___ ps1 ->
                            let x15 =
                              let x16 =
                                let x17 =
                                  FStarC_Tactics_V2_Builtins.term_to_string
                                    ty ps1 in
                                Prims.strcat " of type " x17 in
                              Prims.strcat
                                (FStarC_Reflection_V2_Builtins.implode_qn
                                   c_name) x16 in
                            Prims.strcat "got ctor " x15) ps;
                       (let x15 =
                          FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs ty ps in
                        match x15 with
                        | (bs, cod) ->
                            let x16 =
                              FStar_Tactics_NamedView.inspect_comp cod in
                            (FStar_Tactics_V2_Derived.guard
                               (FStarC_Reflection_V2_Data.uu___is_C_Total x16)
                               ps;
                             (let x18 = x16 in
                              match x18 with
                              | FStarC_Reflection_V2_Data.C_Total cod1 ->
                                  (debug'
                                     (fun uu___ ps1 ->
                                        let x20 =
                                          FStar_Tactics_Util.string_of_list
                                            FStar_Tactics_V2_Derived.binder_to_string
                                            params ps1 in
                                        Prims.strcat "params = " x20) ps;
                                   debug'
                                     (fun uu___ ->
                                        (fun uu___ ->
                                           Obj.magic
                                             (fun uu___1 ->
                                                Prims.strcat "n_params = "
                                                  (Prims.string_of_int
                                                     (FStar_List_Tot_Base.length
                                                        params)))) uu___) ps;
                                   debug'
                                     (fun uu___ ->
                                        (fun uu___ ->
                                           Obj.magic
                                             (fun uu___1 ->
                                                Prims.strcat "n_univs = "
                                                  (Prims.string_of_int
                                                     (FStar_List_Tot_Base.length
                                                        us)))) uu___) ps;
                                   debug'
                                     (fun uu___ ps1 ->
                                        let x23 =
                                          FStarC_Tactics_V2_Builtins.term_to_string
                                            cod1 ps1 in
                                        Prims.strcat "cod = " x23) ps;
                                   (let x23 =
                                      Prims.strcat "__proj__Mk"
                                        (Prims.strcat x11 "__item__") in
                                    let x24 = filter_no_method_binders bs ps in
                                    FStar_Tactics_Util.map
                                      (fun b ps1 ->
                                         let x25 =
                                           FStar_Tactics_V2_Derived.name_of_binder
                                             b ps1 in
                                         debug'
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 Obj.magic
                                                   (fun uu___1 ->
                                                      Prims.strcat
                                                        "processing method "
                                                        x25)) uu___) ps1;
                                         (let x27 =
                                            FStar_Tactics_V2_Derived.cur_module
                                              () ps1 in
                                          let x28 =
                                            FStarC_Reflection_V2_Builtins.pack_fv
                                              ((op_At ()) x27 [x25]) in
                                          let x29 =
                                            FStar_Tactics_V2_Derived.fresh_namedv_named
                                              "d" ps1 in
                                          let x30 =
                                            FStarC_Reflection_V2_Builtins.pack_ln
                                              (FStarC_Reflection_V2_Data.Tv_FVar
                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                    ["FStar";
                                                    "Tactics";
                                                    "Typeclasses";
                                                    "tcresolve"])) in
                                          let x31 =
                                            let x32 =
                                              FStarC_Tactics_V2_Builtins.fresh
                                                () ps1 in
                                            {
                                              FStar_Tactics_NamedView.uniq =
                                                x32;
                                              FStar_Tactics_NamedView.ppname
                                                = (FStar_Sealed.seal "dict");
                                              FStar_Tactics_NamedView.sort =
                                                cod1;
                                              FStar_Tactics_NamedView.qual =
                                                (FStarC_Reflection_V2_Data.Q_Meta
                                                   x30);
                                              FStar_Tactics_NamedView.attrs =
                                                []
                                            } in
                                          let x32 =
                                            let x33 =
                                              FStar_Tactics_V2_Derived.cur_module
                                                () ps1 in
                                            (op_At ()) x33
                                              [Prims.strcat x23 x25] in
                                          let x33 =
                                            FStar_Tactics_NamedView.pack
                                              (FStar_Tactics_NamedView.Tv_FVar
                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                    x32)) in
                                          let x34 =
                                            let x35 =
                                              let x36 =
                                                FStarC_Tactics_V2_Builtins.top_env
                                                  () ps1 in
                                              FStarC_Reflection_V2_Builtins.lookup_typ
                                                x36 x32 in
                                            match x35 with
                                            | FStar_Pervasives_Native.None ->
                                                FStar_Tactics_V2_Derived.fail
                                                  "mk_class: proj not found?"
                                                  ps1
                                            | FStar_Pervasives_Native.Some
                                                se1 -> se1 in
                                          let x35 =
                                            FStarC_Reflection_V2_Builtins.sigelt_attrs
                                              x34 in
                                          let x36 =
                                            let x37 =
                                              FStar_Tactics_NamedView.inspect_sigelt
                                                x34 ps1 in
                                            match x37 with
                                            | FStar_Tactics_NamedView.Sg_Let
                                                {
                                                  FStar_Tactics_NamedView.isrec
                                                    = uu___;
                                                  FStar_Tactics_NamedView.lbs
                                                    = lbs;_}
                                                ->
                                                FStar_Tactics_V2_SyntaxHelpers.lookup_lb
                                                  lbs x32 ps1
                                            | uu___ ->
                                                FStar_Tactics_V2_Derived.fail
                                                  "mk_class: proj not Sg_Let?"
                                                  ps1 in
                                          debug'
                                            (fun uu___ ps2 ->
                                               let x38 =
                                                 FStarC_Tactics_V2_Builtins.term_to_string
                                                   x36.FStar_Tactics_NamedView.lb_typ
                                                   ps2 in
                                               Prims.strcat "proj_ty = " x38)
                                            ps1;
                                          (let x38 =
                                             let x39 =
                                               FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                 x36.FStar_Tactics_NamedView.lb_typ
                                                 ps1 in
                                             match x39 with
                                             | (bs1, cod2) ->
                                                 let x40 =
                                                   FStar_List_Tot_Base.splitAt
                                                     (FStar_List_Tot_Base.length
                                                        params) bs1 in
                                                 (match x40 with
                                                  | (ps2, bs2) ->
                                                      (match bs2 with
                                                       | [] ->
                                                           FStar_Tactics_V2_Derived.fail
                                                             "mk_class: impossible, no binders"
                                                             ps1
                                                       | b1::bs' ->
                                                           let x41 =
                                                             binder_set_meta
                                                               b1 x30 in
                                                           FStar_Tactics_V2_SyntaxHelpers.mk_arr
                                                             ((op_At ()) ps2
                                                                (x41 :: bs'))
                                                             cod2 ps1)) in
                                           let x39 =
                                             let x40 =
                                               FStar_Tactics_V2_SyntaxHelpers.collect_abs
                                                 x36.FStar_Tactics_NamedView.lb_def
                                                 ps1 in
                                             match x40 with
                                             | (bs1, body) ->
                                                 let x41 =
                                                   FStar_List_Tot_Base.splitAt
                                                     (FStar_List_Tot_Base.length
                                                        params) bs1 in
                                                 (match x41 with
                                                  | (ps2, bs2) ->
                                                      (match bs2 with
                                                       | [] ->
                                                           FStar_Tactics_V2_Derived.fail
                                                             "mk_class: impossible, no binders"
                                                             ps1
                                                       | b1::bs' ->
                                                           let x42 =
                                                             binder_set_meta
                                                               b1 x30 in
                                                           mk_abs
                                                             ((op_At ()) ps2
                                                                (x42 :: bs'))
                                                             body ps1)) in
                                           debug'
                                             (fun uu___ ps2 ->
                                                let x41 =
                                                  FStarC_Tactics_V2_Builtins.term_to_string
                                                    x39 ps2 in
                                                Prims.strcat "def = " x41)
                                             ps1;
                                           debug'
                                             (fun uu___ ps2 ->
                                                let x42 =
                                                  FStarC_Tactics_V2_Builtins.term_to_string
                                                    x38 ps2 in
                                                Prims.strcat "ty  = " x42)
                                             ps1;
                                           (let x42 = x38 in
                                            let x43 = x39 in
                                            let x44 = x28 in
                                            let x45 =
                                              {
                                                FStar_Tactics_NamedView.lb_fv
                                                  = x44;
                                                FStar_Tactics_NamedView.lb_us
                                                  =
                                                  (x36.FStar_Tactics_NamedView.lb_us);
                                                FStar_Tactics_NamedView.lb_typ
                                                  = x42;
                                                FStar_Tactics_NamedView.lb_def
                                                  = x43
                                              } in
                                            let x46 =
                                              FStar_Tactics_NamedView.pack_sigelt
                                                (FStar_Tactics_NamedView.Sg_Let
                                                   {
                                                     FStar_Tactics_NamedView.isrec
                                                       = false;
                                                     FStar_Tactics_NamedView.lbs
                                                       = [x45]
                                                   }) ps1 in
                                            FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                                              ((op_At ())
                                                 ((FStarC_Reflection_V2_Builtins.pack_ln
                                                     (FStarC_Reflection_V2_Data.Tv_FVar
                                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                                           ["FStar";
                                                           "Tactics";
                                                           "Typeclasses";
                                                           "tcmethod"]))) ::
                                                 x35)
                                                 b.FStar_Tactics_NamedView.attrs)
                                              (FStarC_Reflection_V2_Builtins.set_sigelt_quals
                                                 x4 x46))))) x24 ps))))))))))))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.mk_class" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.mk_class (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 mk_class)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
let solve (ev : 'a) : 'a= ev
let solve_debug (ev : 'a) : 'a= ev
