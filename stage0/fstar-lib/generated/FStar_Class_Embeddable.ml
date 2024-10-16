open Prims
type 'a embeddable =
  {
  embed: 'a -> FStarC_Reflection_Types.term ;
  typ: FStarC_Reflection_Types.term }
let __proj__Mkembeddable__item__embed :
  'a . 'a embeddable -> 'a -> FStarC_Reflection_Types.term =
  fun projectee -> match projectee with | { embed; typ;_} -> embed
let __proj__Mkembeddable__item__typ :
  'a . 'a embeddable -> FStarC_Reflection_Types.term =
  fun projectee -> match projectee with | { embed; typ;_} -> typ
let embed : 'a . 'a embeddable -> 'a -> FStarC_Reflection_Types.term =
  fun projectee -> match projectee with | { embed = embed1; typ;_} -> embed1
let typ : 'a . 'a embeddable -> FStarC_Reflection_Types.term =
  fun projectee ->
    match projectee with | { embed = embed1; typ = typ1;_} -> typ1
let (embeddable_string : Prims.string embeddable) =
  {
    embed =
      (fun s ->
         FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_Const
              (FStarC_Reflection_V2_Data.C_String s)));
    typ =
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "string"])))
  }
let (embeddable_bool : Prims.bool embeddable) =
  {
    embed =
      (fun b ->
         FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_Const
              (if b
               then FStarC_Reflection_V2_Data.C_True
               else FStarC_Reflection_V2_Data.C_False)));
    typ =
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "bool"])))
  }
let (embeddable_int : Prims.int embeddable) =
  {
    embed =
      (fun i ->
         FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_Const
              (FStarC_Reflection_V2_Data.C_Int i)));
    typ =
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "int"])))
  }
let rec e_list :
  'a . 'a embeddable -> 'a Prims.list -> FStarC_Reflection_Types.term =
  fun ea ->
    fun xs ->
      match xs with
      | [] ->
          let uu___ = ea.typ in
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               ((FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Nil"]))),
                 (uu___, FStarC_Reflection_V2_Data.Q_Implicit)))
      | x::xs1 ->
          let uu___ = e_list ea xs1 in
          let uu___1 = embed ea x in
          let uu___2 = ea.typ in
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               ((FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_App
                      ((FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_App
                             ((FStarC_Reflection_V2_Builtins.pack_ln
                                 (FStarC_Reflection_V2_Data.Tv_FVar
                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                       ["Prims"; "Cons"]))),
                               (uu___2, FStarC_Reflection_V2_Data.Q_Implicit)))),
                        (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))),
                 (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
let embeddable_list : 'a . 'a embeddable -> 'a Prims.list embeddable =
  fun ea ->
    {
      embed = (e_list ea);
      typ =
        (let uu___ = ea.typ in
         FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "list"]))),
                (uu___, FStarC_Reflection_V2_Data.Q_Explicit))))
    }