open Prims
type 'a embeddable =
  {
  embed: 'a -> FStar_Reflection_Types.term ;
  typ: FStar_Reflection_Types.term }
let __proj__Mkembeddable__item__embed :
  'a . 'a embeddable -> 'a -> FStar_Reflection_Types.term =
  fun x4 -> match x4 with | { embed = aembed; typ = atyp;_} -> aembed
let embed : 'a . 'a embeddable -> 'a -> FStar_Reflection_Types.term =
  fun x4 -> __proj__Mkembeddable__item__embed x4
let __proj__Mkembeddable__item__typ :
  'a . 'a embeddable -> FStar_Reflection_Types.term =
  fun x5 -> match x5 with | { embed = aembed; typ = atyp;_} -> atyp
let typ : 'a . 'a embeddable -> FStar_Reflection_Types.term =
  fun x5 -> __proj__Mkembeddable__item__typ x5
let (embeddable_string : Prims.string embeddable) =
  {
    embed =
      (fun s ->
         FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_Const
              (FStar_Reflection_V2_Data.C_String s)));
    typ =
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "string"])))
  }
let (embeddable_bool : Prims.bool embeddable) =
  {
    embed =
      (fun b ->
         FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_Const
              (if b
               then FStar_Reflection_V2_Data.C_True
               else FStar_Reflection_V2_Data.C_False)));
    typ =
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "bool"])))
  }
let (embeddable_int : Prims.int embeddable) =
  {
    embed =
      (fun i ->
         FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_Const
              (FStar_Reflection_V2_Data.C_Int i)));
    typ =
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "int"])))
  }
let rec e_list :
  'a . 'a embeddable -> 'a Prims.list -> FStar_Reflection_Types.term =
  fun ea ->
    fun xs ->
      match xs with
      | [] ->
          let uu___ = ea.typ in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               ((FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_FVar
                      (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "Nil"]))),
                 (uu___, FStar_Reflection_V2_Data.Q_Implicit)))
      | x::xs1 ->
          let uu___ = e_list ea xs1 in
          let uu___1 = embed ea x in
          let uu___2 = ea.typ in
          FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_App
               ((FStar_Reflection_V2_Builtins.pack_ln
                   (FStar_Reflection_V2_Data.Tv_App
                      ((FStar_Reflection_V2_Builtins.pack_ln
                          (FStar_Reflection_V2_Data.Tv_App
                             ((FStar_Reflection_V2_Builtins.pack_ln
                                 (FStar_Reflection_V2_Data.Tv_FVar
                                    (FStar_Reflection_V2_Builtins.pack_fv
                                       ["Prims"; "Cons"]))),
                               (uu___2, FStar_Reflection_V2_Data.Q_Implicit)))),
                        (uu___1, FStar_Reflection_V2_Data.Q_Explicit)))),
                 (uu___, FStar_Reflection_V2_Data.Q_Explicit)))
let embeddable_list : 'a . 'a embeddable -> 'a Prims.list embeddable =
  fun ea ->
    {
      embed = (e_list ea);
      typ =
        (let uu___ = ea.typ in
         FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_App
              ((FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_FVar
                     (FStar_Reflection_V2_Builtins.pack_fv ["Prims"; "list"]))),
                (uu___, FStar_Reflection_V2_Data.Q_Explicit))))
    }