open Prims
type unit_info =
  {
  cu_name: Prims.string FStar_Pervasives_Native.option ;
  cu_headers: Prims.string Prims.list ;
  cu_inits: Prims.string Prims.list ;
  cu_no_prefix: Prims.string Prims.list }
let __proj__Mkunit_info__item__cu_name (projectee : unit_info) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cu_name; cu_headers; cu_inits; cu_no_prefix;_} -> cu_name
let __proj__Mkunit_info__item__cu_headers (projectee : unit_info) :
  Prims.string Prims.list=
  match projectee with
  | { cu_name; cu_headers; cu_inits; cu_no_prefix;_} -> cu_headers
let __proj__Mkunit_info__item__cu_inits (projectee : unit_info) :
  Prims.string Prims.list=
  match projectee with
  | { cu_name; cu_headers; cu_inits; cu_no_prefix;_} -> cu_inits
let __proj__Mkunit_info__item__cu_no_prefix (projectee : unit_info) :
  Prims.string Prims.list=
  match projectee with
  | { cu_name; cu_headers; cu_inits; cu_no_prefix;_} -> cu_no_prefix
let current : Prims.string FStarC_Effect.ref=
  FStarC_Effect.mk_ref "<toplevel>"
let parents : Prims.string FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 50)
let frozen_by : Prims.string FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 20)
let frozen_by_target : Prims.string FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 20)
let existentials : (Prims.string * Prims.string) FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 20)
let root_decls : Prims.bool FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int 50)
let reached_through (n : Prims.string) : Prims.string Prims.list=
  let rec up n1 fuel acc =
    if fuel <= Prims.int_zero
    then FStarC_List.rev acc
    else
      (let uu___ = FStarC_SMap.try_find parents n1 in
       match uu___ with
       | FStar_Pervasives_Native.None -> FStarC_List.rev acc
       | FStar_Pervasives_Native.Some p ->
           up p (fuel - Prims.int_one) (p :: acc)) in
  up n (Prims.of_int 12) []
let chain_entry_width : Prims.int= Prims.of_int 200
let chain_msg (uu___ : unit) : FStar_Pprint.document Prims.list=
  let clip s =
    if (FStarC_String.length s) <= chain_entry_width
    then s
    else
      (let uu___1 =
         FStarC_String.substring s Prims.int_zero chain_entry_width in
       let uu___2 =
         let uu___3 =
           let uu___4 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_nat
               (FStarC_String.length s) in
           Prims.strcat uu___4 " chars)" in
         Prims.strcat " ... (" uu___3 in
       Prims.strcat uu___1 uu___2) in
  let uu___1 =
    let uu___2 = FStarC_Effect.op_Bang current in reached_through uu___2 in
  match uu___1 with
  | [] -> []
  | ns ->
      let uu___2 =
        FStarC_List.map
          (fun n ->
             let uu___3 = let uu___4 = clip n in Prims.strcat "  " uu___4 in
             FStarC_Errors_Msg.text uu___3) ns in
      (FStarC_Errors_Msg.text "Reached through:") :: uu___2
let existential_msg (uu___ : unit) : FStar_Pprint.document Prims.list=
  let rec first ns =
    match ns with
    | [] -> []
    | n::ns1 ->
        let uu___1 = FStarC_SMap.try_find existentials n in
        (match uu___1 with
         | FStar_Pervasives_Native.Some (c, f) ->
             [FStarC_Errors_Msg.text
                (Prims.strcat n
                   (Prims.strcat
                      " is an existential package, not an instance of a parameterized type: its constructor "
                      (Prims.strcat c
                         (Prims.strcat " stores the type "
                            (Prims.strcat f
                               ", and a later field's type mentions it, so its representation depends on its contents (section 30.3).")))));
             FStarC_Errors_Msg.text
               "That is why the representation above is unknown, and it is not a Custard bug: no C layout exists for it, and no annotation changes that.  Replace the stored type by an index the program can case on, or make it a parameter of the type rather than a field of the constructor."]
         | FStar_Pervasives_Native.None -> first ns1) in
  let uu___1 =
    let uu___2 = FStarC_Effect.op_Bang current in
    let uu___3 =
      let uu___4 = FStarC_Effect.op_Bang current in reached_through uu___4 in
    uu___2 :: uu___3 in
  first uu___1
let reject (what : Prims.string) (why : Prims.string Prims.list) : 'a=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Effect.op_Bang current in
                Prims.strcat uu___7 "." in
              Prims.strcat " has no C representation, in " uu___6 in
            Prims.strcat what uu___5 in
          Prims.strcat "Custard: " uu___4 in
        FStarC_Errors_Msg.text uu___3 in
      [uu___2] in
    let uu___2 =
      let uu___3 = FStarC_List.map FStarC_Errors_Msg.text why in
      let uu___4 =
        let uu___5 = existential_msg () in
        let uu___6 = chain_msg () in FStarC_List.op_At uu___5 uu___6 in
      FStarC_List.op_At uu___3 uu___4 in
    FStarC_List.op_At uu___1 uu___2 in
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let reject_ir (what : Prims.string) (why : Prims.string Prims.list) : 
  'a=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Effect.op_Bang current in
                Prims.strcat uu___7 "." in
              Prims.strcat " reached the C backend, in " uu___6 in
            Prims.strcat what uu___5 in
          Prims.strcat "Custard: " uu___4 in
        FStarC_Errors_Msg.text uu___3 in
      [uu___2] in
    let uu___2 =
      let uu___3 = FStarC_List.map FStarC_Errors_Msg.text why in
      let uu___4 = chain_msg () in FStarC_List.op_At uu___3 uu___4 in
    FStarC_List.op_At uu___1 uu___2 in
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let c_keywords : Prims.string Prims.list=
  ["auto";
  "break";
  "case";
  "char";
  "const";
  "continue";
  "default";
  "do";
  "double";
  "else";
  "enum";
  "extern";
  "float";
  "for";
  "goto";
  "if";
  "inline";
  "int";
  "long";
  "register";
  "restrict";
  "return";
  "short";
  "signed";
  "sizeof";
  "static";
  "struct";
  "switch";
  "typedef";
  "union";
  "unsigned";
  "void";
  "volatile";
  "while";
  "_Bool";
  "_Complex";
  "_Imaginary";
  "bool";
  "true";
  "false";
  "NULL";
  "main"]
let is_alpha (i : Prims.int) : Prims.bool=
  ((i >= (Prims.of_int 97)) && (i <= (Prims.of_int 122))) ||
    ((i >= (Prims.of_int 65)) && (i <= (Prims.of_int 90)))
let sanitize (s : Prims.string) : Prims.string=
  let ok i =
    ((is_alpha i) || ((i >= (Prims.of_int 48)) && (i <= (Prims.of_int 57))))
      || (i = (Prims.of_int 95)) in
  match FStarC_String.list_of_string s with
  | [] -> "x"
  | c0::cs ->
      let s1 =
        let uu___ =
          FStarC_List.map
            (fun c ->
               if ok (FStarC_Util.int_of_char c)
               then FStarC_Util.string_of_char c
               else "_") (c0 :: cs) in
        FStarC_String.concat "" uu___ in
      let i0 = FStarC_Util.int_of_char c0 in
      let i01 = if ok i0 then i0 else Prims.of_int 95 in
      if (is_alpha i01) || (i01 = (Prims.of_int 95))
      then s1
      else Prims.strcat "x" s1
let is_group (s : Prims.string) : Prims.bool=
  let n = FStarC_String.length s in
  let uu___ =
    let uu___1 =
      if n < (Prims.of_int 2)
      then true
      else
        (let uu___2 = FStarC_String.substring s Prims.int_zero Prims.int_one in
         uu___2 <> "(") in
    if uu___1
    then true
    else
      (let uu___2 =
         FStarC_String.substring s (n - Prims.int_one) Prims.int_one in
       uu___2 <> ")") in
  if uu___
  then false
  else
    (let cs = FStarC_String.list_of_string s in
     let rec scan cs1 i depth =
       match cs1 with
       | [] -> true
       | c::rest ->
           let d =
             if (FStarC_Util.int_of_char c) = (Prims.of_int 40)
             then depth + Prims.int_one
             else
               if (FStarC_Util.int_of_char c) = (Prims.of_int 41)
               then depth - Prims.int_one
               else depth in
           if (d = Prims.int_zero) && (i < (n - Prims.int_one))
           then false
           else scan rest (i + Prims.int_one) d in
     scan cs Prims.int_zero Prims.int_zero)
let unparen (s : Prims.string) : Prims.string=
  let uu___ = is_group s in
  if uu___
  then
    FStarC_String.substring s Prims.int_one
      ((FStarC_String.length s) - (Prims.of_int 2))
  else s
let is_atom (s : Prims.string) : Prims.bool=
  let uu___ =
    if s <> ""
    then
      let uu___1 = FStarC_String.get s Prims.int_zero in
      FStarC_Util.is_digit uu___1
    else false in
  if uu___
  then
    FStarC_List.for_all
      (fun c -> (FStarC_Util.is_letter_or_digit c) || (c = 95))
      (FStarC_String.list_of_string s)
  else false
let group (s : Prims.string) : Prims.string=
  let uu___ = let uu___1 = is_group s in if uu___1 then true else is_atom s in
  if uu___ then s else Prims.strcat "(" (Prims.strcat s ")")
let negate (s : Prims.string) : Prims.string=
  let uu___ = group s in Prims.strcat "!" uu___
let escape_kw (s : Prims.string) : Prims.string=
  let rec strip t =
    let n = FStarC_String.length t in
    let uu___ =
      if n > Prims.int_zero
      then
        let uu___1 =
          FStarC_String.substring t (n - Prims.int_one) Prims.int_one in
        uu___1 = "_"
      else false in
    if uu___
    then
      let uu___1 =
        FStarC_String.substring t Prims.int_zero (n - Prims.int_one) in
      strip uu___1
    else t in
  let uu___ =
    FStarC_List.existsb (fun k -> let uu___1 = strip s in k = uu___1)
      c_keywords in
  if uu___ then Prims.strcat s "_" else s
let renames : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let macros : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let c_name (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang macros in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | FStar_Pervasives_Native.Some s -> s
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang renames in
        let uu___3 = FStarC_Custard_Syntax.string_of_name n in
        FStarC_SMap.try_find uu___2 uu___3 in
      (match uu___1 with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None ->
           let uu___2 =
             let uu___3 = FStarC_Custard_Syntax.mangled_name n in
             sanitize uu___3 in
           escape_kw uu___2)
let c_var (x : Prims.string) : Prims.string=
  let uu___ = sanitize x in escape_kw uu___
let extern_target (d : FStarC_Custard_Syntax.decl) :
  Prims.string FStar_Pervasives_Native.option=
  match d with
  | FStarC_Custard_Syntax.DExternal x ->
      (match x.FStarC_Custard_Syntax.dx_target with
       | FStar_Pervasives_Native.Some "" -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t)
  | uu___ -> FStar_Pervasives_Native.None
let emitted_name (d : FStarC_Custard_Syntax.decl) : Prims.string=
  let uu___ = extern_target d in
  match uu___ with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None ->
      c_name (FStarC_Custard_Syntax.name_of_decl d)
let arm_name (cn : FStarC_Custard_Syntax.name) : Prims.string=
  c_var cn.FStarC_Custard_Syntax.id
let arm_flat (fs : (Prims.string * FStarC_Custard_Syntax.cty) Prims.list) :
  Prims.bool= match fs with | uu___::[] -> true | uu___ -> false
let arm_sel (cn : FStarC_Custard_Syntax.name)
  (fs : (Prims.string * FStarC_Custard_Syntax.cty) Prims.list)
  (f : Prims.string) : Prims.string=
  let uu___ =
    let uu___1 = arm_name cn in
    let uu___2 =
      if arm_flat fs
      then ""
      else (let uu___3 = c_var f in Prims.strcat "." uu___3) in
    Prims.strcat uu___1 uu___2 in
  Prims.strcat ".val." uu___
let c_tag (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Effect.op_Bang renames in
      let uu___3 = FStarC_Custard_Syntax.string_of_name n in
      FStarC_SMap.try_find uu___2 uu___3 in
    match uu___1 with
    | FStar_Pervasives_Native.Some s -> s
    | FStar_Pervasives_Native.None ->
        let uu___2 = FStarC_Custard_Syntax.mangled_name n in sanitize uu___2 in
  FStarC_String.uppercase uu___
let types : FStarC_Custard_Syntax.dtype FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let ctors :
  (FStarC_Custard_Syntax.dtype * (Prims.string * FStarC_Custard_Syntax.cty)
    Prims.list) FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let externs : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let keeps : Prims.bool Prims.list FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let void_fns : Prims.bool FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let arities : Prims.int FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let void_ret : Prims.bool FStarC_Effect.ref= FStarC_Effect.mk_ref false
let rec filter_by :
  'a . Prims.bool Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun flags xs ->
    match (flags, xs) with
    | (b::flags1, x::xs1) ->
        FStarC_List.op_At (if b then [x] else []) (filter_by flags1 xs1)
    | uu___ -> xs
let find_type (n : FStarC_Custard_Syntax.name) :
  FStarC_Custard_Syntax.dtype FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang types in
  let uu___1 = FStarC_Custard_Syntax.string_of_name n in
  FStarC_SMap.try_find uu___ uu___1
let extern_template_of (n : FStarC_Custard_Syntax.name) :
  FStarC_Custard_Syntax.tmpl_piece Prims.list FStar_Pervasives_Native.option=
  let uu___ = find_type n in
  match uu___ with
  | FStar_Pervasives_Native.Some
      { FStarC_Custard_Syntax.dt_name = uu___1;
        FStarC_Custard_Syntax.dt_params = uu___2;
        FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TAbstract;
        FStarC_Custard_Syntax.dt_flags = fs;_}
      -> FStarC_Custard_Syntax.extern_template_of_flags fs
  | uu___1 -> FStar_Pervasives_Native.None
let binds_by_ref (t : FStarC_Custard_Syntax.cty) : Prims.bool=
  match t with
  | FStarC_Custard_Syntax.TApp (n, uu___) ->
      let uu___1 = find_type n in
      (match uu___1 with
       | FStar_Pervasives_Native.Some
           { FStarC_Custard_Syntax.dt_name = uu___2;
             FStarC_Custard_Syntax.dt_params = uu___3;
             FStarC_Custard_Syntax.dt_body = uu___4;
             FStarC_Custard_Syntax.dt_flags = fs;_}
           -> FStarC_List.existsb FStarC_Custard_Syntax.uu___is_CReference fs
       | uu___2 -> false)
  | uu___ -> false
let find_ctor (n : FStarC_Custard_Syntax.name) :
  (FStarC_Custard_Syntax.dtype * (Prims.string * FStarC_Custard_Syntax.cty)
    Prims.list) FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang ctors in
  let uu___1 = FStarC_Custard_Syntax.string_of_name n in
  FStarC_SMap.try_find uu___ uu___1
let single_ctor (d : FStarC_Custard_Syntax.dtype) : Prims.bool=
  match d.FStarC_Custard_Syntax.dt_body with
  | FStarC_Custard_Syntax.TVariant (uu___::[]) -> true
  | uu___ -> false
let is_enum (d : FStarC_Custard_Syntax.dtype) : Prims.bool=
  match d.FStarC_Custard_Syntax.dt_body with
  | FStarC_Custard_Syntax.TVariant cs ->
      if (match cs with | hd::tl -> true | uu___ -> false)
      then
        FStarC_List.for_all
          (fun uu___ ->
             match uu___ with
             | (uu___1, fs) -> (match fs with | [] -> true | uu___2 -> false))
          cs
      else false
  | uu___ -> false
let sizet_narrow (uu___ : unit) : Prims.bool=
  FStarC_Options.custard_sizet_32 ()
let int_type (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  : Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      (match w with
       | FStarC_Custard_Syntax.WSizet ->
           let uu___1 = sizet_narrow () in
           if uu___1 then "uint32_t" else "size_t"
       | FStarC_Custard_Syntax.W128 ->
           (match s with
            | FStarC_Const.Unsigned -> "unsigned __int128"
            | FStarC_Const.Signed -> "__int128")
       | uu___1 ->
           Prims.strcat
             (match s with
              | FStarC_Const.Unsigned -> "uint"
              | FStarC_Const.Signed -> "int")
             (Prims.strcat
                (match w with
                 | FStarC_Custard_Syntax.W8 -> "8"
                 | FStarC_Custard_Syntax.W16 -> "16"
                 | FStarC_Custard_Syntax.W32 -> "32"
                 | FStarC_Custard_Syntax.W64 -> "64"
                 | FStarC_Custard_Syntax.W128 -> ""
                 | FStarC_Custard_Syntax.WSizet -> "") "_t"))
let mono_advice_for
  (n : FStarC_Custard_Syntax.name FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  let uu___ =
    let uu___1 = FStarC_Options.custard_monomorphize_types () in
    Prims.not uu___1 in
  if uu___
  then
    ["The direct-to-C backend requires --custard_monomorphize_types true (section 5.0.1)."]
  else
    (let uu___1 =
       match n with
       | uu___2 when
           let uu___3 = FStarC_Options.custard_backend () in
           uu___3 <> "OCaml" -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some n1 ->
           let uu___2 = FStarC_Custard_Syntax.string_of_name n1 in
           FStarC_SMap.try_find frozen_by uu___2 in
     match uu___1 with
     | FStar_Pervasives_Native.Some ext ->
         let where =
           let uu___2 =
             match n with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some n1 ->
                 let uu___3 = FStarC_Custard_Syntax.string_of_name n1 in
                 FStarC_SMap.try_find frozen_by_target uu___3 in
           match uu___2 with
           | FStar_Pervasives_Native.Some sym ->
               Prims.strcat "it is the C symbol `"
                 (Prims.strcat sym
                    "', named by a custard_extern attribute, and that symbol's own declaration decides the layout")
           | FStar_Pervasives_Native.None ->
               "it is a hand-written realization for the OCaml backend, and there is no C counterpart" in
         [Prims.strcat
            "--custard_monomorphize_types is set, and the pass deliberately left this type alone: it is mentioned in the signature of "
            (Prims.strcat ext
               ", which is realized outside this program, so a monomorphic clone of it would name a declaration the realization does not define (section 5.0.1, rule 4).");
         Prims.strcat "The type is frozen because "
           (Prims.strcat ext
              (Prims.strcat
                 " is external, not because it could not be sized.  Give "
                 (Prims.strcat ext
                    (Prims.strcat " a definition Custard can compile -- "
                       (Prims.strcat where
                          " -- or keep this type out of its signature.")))))]
     | FStar_Pervasives_Native.None ->
         let uu___2 =
           let uu___3 = existential_msg () in
           match uu___3 with | hd::tl -> true | uu___4 -> false in
         if uu___2
         then
           ["--custard_monomorphize_types is already set, so nothing was left polymorphic by choice; the reason is below."]
         else
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Effect.op_Bang current in
                FStarC_SMap.try_find root_decls uu___5 in
              match uu___4 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___5 -> false in
            if uu___3
            then
              ["This declaration is a root, and a root has no call site.  Specialization takes its type arguments from callers, so a root that is still polymorphic has nothing to be specialized against -- which is a fact about what was asked for, not a Custard bug.";
              "--custard_entry_module roots every definition in a module, including polymorphic helpers that the program only ever calls at concrete types.  Those are skipped now (section 72.1); this one was named directly, so it was taken at its word.";
              "Root a concrete caller of it instead -- --custard_entry on the definition that applies it -- or, if it is meant to be called from outside the program, give it a monomorphic signature."]
            else
              ["--custard_monomorphize_types is already set, so this type is one the monomorphization pass did not reach (section 5.0.1).";
              "That is a Custard bug, not a configuration problem: please report it, with the definition named above."]))
let mono_advice (uu___ : unit) : Prims.string Prims.list=
  mono_advice_for FStar_Pervasives_Native.None
let builtin_type (n : FStarC_Custard_Syntax.name) :
  Prims.string FStar_Pervasives_Native.option=
  match if
          match n.FStarC_Custard_Syntax.spec with
          | FStar_Pervasives_Native.Some v -> true
          | uu___ -> false
        then ""
        else
          FStarC_String.concat "."
            (FStarC_List.op_At n.FStarC_Custard_Syntax.ns
               [n.FStarC_Custard_Syntax.id])
  with
  | "Prims.unit" -> FStar_Pervasives_Native.Some "custard_unit"
  | "Prims.bool" -> FStar_Pervasives_Native.Some "bool"
  | "Prims.string" -> FStar_Pervasives_Native.Some "const char *"
  | "FStar.Char.char" -> FStar_Pervasives_Native.Some "uint32_t"
  | uu___ -> FStar_Pervasives_Native.None
let is_string_ty (t : FStarC_Custard_Syntax.cty) : Prims.bool=
  match t with
  | FStarC_Custard_Syntax.TApp (n, []) ->
      (match n.FStarC_Custard_Syntax.spec with
       | FStar_Pervasives_Native.None -> true
       | uu___ -> false) &&
        ((FStarC_String.concat "."
            (FStarC_List.op_At n.FStarC_Custard_Syntax.ns
               [n.FStarC_Custard_Syntax.id]))
           = "Prims.string")
  | uu___ -> false
let rec decl_of (t : FStarC_Custard_Syntax.cty) (x : Prims.string) :
  Prims.string=
  match t with
  | FStarC_Custard_Syntax.TBuf e -> decl_of e (Prims.strcat "*" x)
  | FStarC_Custard_Syntax.TRef e -> decl_of e (Prims.strcat "*" x)
  | FStarC_Custard_Syntax.TArrow uu___ ->
      let rec spine t1 acc =
        match t1 with
        | FStarC_Custard_Syntax.TArrow (a, uu___1, b) -> spine b (a :: acc)
        | uu___1 -> ((FStarC_List.rev acc), t1) in
      let uu___1 = spine t [] in
      (match uu___1 with
       | (args, ret) ->
           let args1 =
             FStarC_List.filter
               (fun a ->
                  Prims.not
                    (match a with
                     | FStarC_Custard_Syntax.TUnit -> true
                     | uu___2 -> false)) args in
           let inner =
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     match args1 with
                     | [] -> "void"
                     | uu___6 ->
                         let uu___7 =
                           FStarC_List.map (fun a -> decl_of a "") args1 in
                         FStarC_String.concat ", " uu___7 in
                   Prims.strcat uu___5 ")" in
                 Prims.strcat ")(" uu___4 in
               Prims.strcat x uu___3 in
             Prims.strcat "(*" uu___2 in
           if
             (match ret with
              | FStarC_Custard_Syntax.TUnit -> true
              | uu___2 -> false)
           then Prims.strcat "void " inner
           else decl_of ret inner)
  | uu___ ->
      let uu___1 = base_ty t in
      Prims.strcat uu___1 (if x = "" then "" else Prims.strcat " " x)
and base_ty (t : FStarC_Custard_Syntax.cty) : Prims.string=
  match t with
  | FStarC_Custard_Syntax.TInline uu___ ->
      FStarC_Effect.failwith
        "Custard: an inline-field marker reached the C backend"
  | FStarC_Custard_Syntax.TUnit -> "custard_unit"
  | FStarC_Custard_Syntax.TInt sw -> int_type sw
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float32) -> "float"
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float64) -> "double"
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float16) ->
      "custard_f16"
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.BFloat16) ->
      "custard_bf16"
  | FStarC_Custard_Syntax.TConst (FStarC_Custard_Syntax.CInt (v, b, uu___))
      -> FStarC_Custard_Syntax.c_int_lit_to_string v b
  | FStarC_Custard_Syntax.TConst (FStarC_Custard_Syntax.CBool b) ->
      if b then "true" else "false"
  | FStarC_Custard_Syntax.TConst c ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [FStarC_Errors_Msg.text
              "Custard: this external type is applied to a constant that cannot be a template argument.";
           FStarC_Errors_Msg.text
             "A non-type template parameter may be an integer or a bool.  A float, a character or a string is not one, and neither is unit."])
  | FStarC_Custard_Syntax.TApp (n, args) when
      let uu___ = extern_template_of n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let ps =
        let uu___ = extern_template_of n in
        match uu___ with
        | FStar_Pervasives_Native.Some ps1 -> ps1
        | FStar_Pervasives_Native.None -> [] in
      let uu___ =
        FStarC_List.map
          (fun p ->
             match p with
             | FStarC_Custard_Syntax.TP_lit s -> s
             | FStarC_Custard_Syntax.TP_arg i ->
                 (match FStar_Pervasives_Native.snd
                          (FStarC_List.splitAt i args)
                  with
                  | a::uu___1 -> base_ty a
                  | [] ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                FStarC_Custard_Syntax.string_of_name n in
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_int i in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        FStarC_Class_Show.show
                                          FStarC_Class_Show.showable_nat
                                          (FStarC_List.length args) in
                                      Prims.strcat uu___11 " argument(s)." in
                                    Prims.strcat ", but the type has only "
                                      uu___10 in
                                  Prims.strcat uu___8 uu___9 in
                                Prims.strcat " mentions argument " uu___7 in
                              Prims.strcat uu___5 uu___6 in
                            Prims.strcat
                              "Custard: the target of the external type "
                              uu___4 in
                          FStarC_Errors_Msg.text uu___3 in
                        [uu___2;
                        FStarC_Errors_Msg.text
                          "The placeholders in a [@@custard_extern] string count the declaration's binders from zero, all of them, in source order."] in
                      FStarC_Errors.raise_error0
                        FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
                        (Obj.magic
                           FStarC_Errors_Msg.is_error_message_list_doc)
                        (Obj.magic uu___1))) ps in
      FStarC_String.concat "" uu___
  | FStarC_Custard_Syntax.TApp (n, []) ->
      let uu___ = builtin_type n in
      (match uu___ with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None ->
           let uu___1 = find_type n in
           (match uu___1 with
            | FStar_Pervasives_Native.Some
                { FStarC_Custard_Syntax.dt_name = uu___2;
                  FStarC_Custard_Syntax.dt_params = uu___3;
                  FStarC_Custard_Syntax.dt_body =
                    FStarC_Custard_Syntax.TAbstract;
                  FStarC_Custard_Syntax.dt_flags = fs;_}
                when
                FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Extern fs
                ->
                let uu___4 =
                  FStarC_List.tryPick
                    (fun f ->
                       match f with
                       | FStarC_Custard_Syntax.Extern (t1, uu___5) -> t1
                       | uu___5 -> FStar_Pervasives_Native.None) fs in
                (match uu___4 with
                 | FStar_Pervasives_Native.Some t1 -> t1
                 | FStar_Pervasives_Native.None -> c_name n)
            | FStar_Pervasives_Native.Some
                { FStarC_Custard_Syntax.dt_name = uu___2;
                  FStarC_Custard_Syntax.dt_params = uu___3;
                  FStarC_Custard_Syntax.dt_body =
                    FStarC_Custard_Syntax.TAbstract;
                  FStarC_Custard_Syntax.dt_flags = uu___4;_}
                ->
                let uu___5 =
                  let uu___6 = FStarC_Custard_Syntax.string_of_name n in
                  Prims.strcat "the abstract type " uu___6 in
                reject uu___5
                  ["A type with no definition has no size, so C cannot store it.";
                  "Prims.int in particular is unbounded: use a machine integer type instead."]
            | uu___2 -> c_name n))
  | FStarC_Custard_Syntax.TApp (n, uu___) ->
      let uu___1 =
        let uu___2 = FStarC_Custard_Syntax.string_of_name n in
        Prims.strcat "the polymorphic type " uu___2 in
      let uu___2 = mono_advice_for (FStar_Pervasives_Native.Some n) in
      reject uu___1 uu___2
  | FStarC_Custard_Syntax.TVar x ->
      let uu___ = mono_advice () in
      reject (Prims.strcat "the type variable '" x) uu___
  | FStarC_Custard_Syntax.TTuple uu___ ->
      reject "an anonymous tuple type"
        ["Tuples reach the backend as FStar.Pervasives.Native.tupleN, which is an ordinary inductive; a bare TTuple means a rule introduced one."]
  | FStarC_Custard_Syntax.TAny ->
      reject "a value whose representation is unknown (TAny)"
        ["Run with --custard_warn_any to see where the representation was lost (section 5.9)."]
  | FStarC_Custard_Syntax.TExn ->
      reject "an exception type" ["C has no exceptions."]
  | FStarC_Custard_Syntax.TBuf uu___ -> decl_of t ""
  | FStarC_Custard_Syntax.TRef uu___ -> decl_of t ""
  | FStarC_Custard_Syntax.TArrow uu___ -> decl_of t ""
let ty (t : FStarC_Custard_Syntax.cty) : Prims.string= decl_of t ""
let eq_queue :
  (Prims.string * FStarC_Custard_Syntax.dtype) Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let eq_seen : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create (Prims.of_int 20) in
  FStarC_Effect.mk_ref uu___
let taken_names : Prims.bool FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_Effect.mk_ref uu___
let alloc_name (base : Prims.string) : Prims.string=
  let rec go cand n =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang taken_names in
        FStarC_SMap.try_find uu___2 cand in
      match uu___1 with
      | FStar_Pervasives_Native.None -> true
      | uu___2 -> false in
    if uu___
    then cand
    else
      go (Prims.strcat base (Prims.strcat "_" (Prims.string_of_int n)))
        (n + Prims.int_one) in
  let f = go base Prims.int_one in
  (let uu___1 = FStarC_Effect.op_Bang taken_names in
   FStarC_SMap.add uu___1 f true);
  f
let rec eq_target (t : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.dtype FStar_Pervasives_Native.option=
  match t with
  | FStarC_Custard_Syntax.TApp (n, []) when
      let uu___ = builtin_type n in
      match uu___ with
      | FStar_Pervasives_Native.None -> true
      | uu___1 -> false ->
      let uu___ = find_type n in
      (match uu___ with
       | FStar_Pervasives_Native.Some d when
           FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Extern
             d.FStarC_Custard_Syntax.dt_flags
           -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some d ->
           (match d.FStarC_Custard_Syntax.dt_body with
            | FStarC_Custard_Syntax.TAbbrev u -> eq_target u
            | FStarC_Custard_Syntax.TRecord uu___1 ->
                FStar_Pervasives_Native.Some d
            | FStarC_Custard_Syntax.TVariant uu___1 ->
                let uu___2 = is_enum d in
                if uu___2
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some d
            | FStarC_Custard_Syntax.TAbstract -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let eq_fn_of (t : FStarC_Custard_Syntax.cty) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = eq_target t in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let k =
        FStarC_Custard_Syntax.string_of_name d.FStarC_Custard_Syntax.dt_name in
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang eq_seen in
        FStarC_SMap.try_find uu___2 k in
      (match uu___1 with
       | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
       | FStar_Pervasives_Native.None ->
           let f =
             let uu___2 =
               let uu___3 = c_name d.FStarC_Custard_Syntax.dt_name in
               Prims.strcat uu___3 "__eq" in
             alloc_name uu___2 in
           ((let uu___3 = FStarC_Effect.op_Bang eq_seen in
             FStarC_SMap.add uu___3 k f);
            (let uu___4 =
               let uu___5 = FStarC_Effect.op_Bang eq_queue in
               FStarC_List.op_At uu___5 [(f, d)] in
             FStarC_Effect.op_Colon_Equals eq_queue uu___4);
            FStar_Pervasives_Native.Some f))
let eq_proto (f : Prims.string) (d : FStarC_Custard_Syntax.dtype) :
  Prims.string=
  let n = c_name d.FStarC_Custard_Syntax.dt_name in
  Prims.strcat "static bool "
    (Prims.strcat f
       (Prims.strcat "("
          (Prims.strcat n (Prims.strcat " a, " (Prims.strcat n " b);\n")))))
let eq_def (f : Prims.string) (d : FStarC_Custard_Syntax.dtype) :
  Prims.string=
  let n = c_name d.FStarC_Custard_Syntax.dt_name in
  let hd =
    Prims.strcat "static bool "
      (Prims.strcat f
         (Prims.strcat "("
            (Prims.strcat n (Prims.strcat " a, " (Prims.strcat n " b) {\n"))))) in
  let cmp a b t =
    let uu___ = is_string_ty t in
    if uu___
    then
      Prims.strcat "strcmp("
        (Prims.strcat a (Prims.strcat ", " (Prims.strcat b ") == 0")))
    else
      (let uu___1 = eq_fn_of t in
       match uu___1 with
       | FStar_Pervasives_Native.Some g ->
           Prims.strcat g
             (Prims.strcat "("
                (Prims.strcat a (Prims.strcat ", " (Prims.strcat b ")"))))
       | FStar_Pervasives_Native.None ->
           Prims.strcat "("
             (Prims.strcat a (Prims.strcat " == " (Prims.strcat b ")")))) in
  let all pa pb fs =
    match fs with
    | [] -> "true"
    | uu___ ->
        let uu___1 =
          FStarC_List.map
            (fun uu___2 ->
               match uu___2 with
               | (g, t) ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = c_var g in Prims.strcat "." uu___5 in
                     Prims.strcat pa uu___4 in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = c_var g in Prims.strcat "." uu___6 in
                     Prims.strcat pb uu___5 in
                   cmp uu___3 uu___4 t) fs in
        FStarC_String.concat " && " uu___1 in
  let trivial = "  (void)a; (void)b;\n  return true;\n}\n" in
  let direct fs =
    if match fs with | [] -> true | uu___ -> false
    then Prims.strcat hd trivial
    else
      (let uu___ =
         let uu___1 =
           let uu___2 = all "a" "b" fs in Prims.strcat uu___2 ";\n}\n" in
         Prims.strcat "  return " uu___1 in
       Prims.strcat hd uu___) in
  match d.FStarC_Custard_Syntax.dt_body with
  | FStarC_Custard_Syntax.TRecord fs -> direct fs
  | FStarC_Custard_Syntax.TVariant cs when single_ctor d ->
      direct (FStar_Pervasives_Native.snd (FStarC_List.hd cs))
  | FStarC_Custard_Syntax.TVariant cs ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_List.map
                  (fun uu___5 ->
                     match uu___5 with
                     | (cn, fs) ->
                         let uu___6 =
                           let uu___7 = c_tag cn in
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 if
                                   match fs with
                                   | [] -> true
                                   | uu___11 -> false
                                 then "true"
                                 else
                                   if arm_flat fs
                                   then
                                     (let uu___11 =
                                        let uu___12 = arm_name cn in
                                        Prims.strcat "a.val." uu___12 in
                                      let uu___12 =
                                        let uu___13 = arm_name cn in
                                        Prims.strcat "b.val." uu___13 in
                                      cmp uu___11 uu___12
                                        (FStar_Pervasives_Native.snd
                                           (FStarC_List.hd fs)))
                                   else
                                     (let uu___11 =
                                        let uu___12 = arm_name cn in
                                        Prims.strcat "a.val." uu___12 in
                                      let uu___12 =
                                        let uu___13 = arm_name cn in
                                        Prims.strcat "b.val." uu___13 in
                                      all uu___11 uu___12 fs) in
                               Prims.strcat uu___10 ";\n" in
                             Prims.strcat ": return " uu___9 in
                           Prims.strcat uu___7 uu___8 in
                         Prims.strcat "    case " uu___6) cs in
              FStarC_String.concat "" uu___4 in
            Prims.strcat uu___3 "  }\n  return true;\n}\n" in
          Prims.strcat "  switch (a.tag) {\n" uu___2 in
        Prims.strcat "  if (a.tag != b.tag) return false;\n" uu___1 in
      Prims.strcat hd uu___
  | uu___ -> Prims.strcat hd trivial
let eq_decls (uu___ : unit) :
  (Prims.string Prims.list * Prims.string Prims.list)=
  let protos = FStarC_Effect.mk_ref [] in
  let defs = FStarC_Effect.mk_ref [] in
  let rec go fuel =
    if fuel <= Prims.int_zero
    then FStarC_Effect.failwith "Custard: generated equalities do not settle"
    else
      (let uu___1 = FStarC_Effect.op_Bang eq_queue in
       match uu___1 with
       | [] -> ()
       | (f, d)::rest ->
           (FStarC_Effect.op_Colon_Equals eq_queue rest;
            (let uu___4 =
               let uu___5 = FStarC_Effect.op_Bang protos in
               let uu___6 = let uu___7 = eq_proto f d in [uu___7] in
               FStarC_List.op_At uu___5 uu___6 in
             FStarC_Effect.op_Colon_Equals protos uu___4);
            (let uu___5 =
               let uu___6 = FStarC_Effect.op_Bang defs in
               let uu___7 = let uu___8 = eq_def f d in [uu___8] in
               FStarC_List.op_At uu___6 uu___7 in
             FStarC_Effect.op_Colon_Equals defs uu___5);
            go (fuel - Prims.int_one))) in
  go (Prims.of_int 10000);
  (let uu___2 = FStarC_Effect.op_Bang protos in
   let uu___3 = FStarC_Effect.op_Bang defs in (uu___2, uu___3))
let unit_value : Prims.string= "((custard_unit)0)"
let int_suffix
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      let wide =
        match w with
        | FStarC_Custard_Syntax.W64 -> true
        | FStarC_Custard_Syntax.W128 -> true
        | FStarC_Custard_Syntax.WSizet ->
            let uu___1 = sizet_narrow () in Prims.not uu___1
        | uu___1 -> false in
      (match s with
       | FStarC_Const.Unsigned -> if wide then "ULL" else "U"
       | FStarC_Const.Signed -> if wide then "LL" else "")
let int_literal
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (v : Prims.int) (b : FStar_IntegerLiteral.int_base) : Prims.string=
  let uu___ = sw in
  match uu___ with
  | (sg, w) ->
      let wide =
        match w with
        | FStarC_Custard_Syntax.W64 -> true
        | FStarC_Custard_Syntax.WSizet ->
            let uu___1 = sizet_narrow () in Prims.not uu___1
        | uu___1 -> false in
      if w = FStarC_Custard_Syntax.W128
      then
        let neg = v < Prims.int_zero in
        let a = if neg then - v else v in
        let lo = (mod) a (Prims.parse_int "18446744073709551616") in
        let hi = a / (Prims.parse_int "18446744073709551616") in
        let u = "(unsigned __int128)" in
        (if (hi = Prims.int_zero) && (Prims.not neg)
         then
           let uu___1 =
             let uu___2 = int_type sw in
             Prims.strcat uu___2
               (Prims.strcat ")"
                  (Prims.strcat
                     (FStarC_Custard_Syntax.c_int_lit_to_string lo b) "ULL)")) in
           Prims.strcat "((" uu___1
         else
           (let mag =
              if hi = Prims.int_zero
              then
                Prims.strcat "("
                  (Prims.strcat u
                     (Prims.strcat
                        (FStarC_Custard_Syntax.c_int_lit_to_string lo b)
                        "ULL)"))
              else
                Prims.strcat "(("
                  (Prims.strcat u
                     (Prims.strcat
                        (FStarC_Custard_Syntax.c_int_lit_to_string hi b)
                        (Prims.strcat "ULL << 64) | "
                           (Prims.strcat u
                              (Prims.strcat
                                 (FStarC_Custard_Syntax.c_int_lit_to_string
                                    lo b) "ULL)"))))) in
            let e =
              if neg then Prims.strcat "(-" (Prims.strcat mag ")") else mag in
            if match sg with | FStarC_Const.Signed -> true | uu___1 -> false
            then
              let uu___1 =
                let uu___2 = int_type sw in
                Prims.strcat uu___2 (Prims.strcat ")" (Prims.strcat e ")")) in
              Prims.strcat "((" uu___1
            else e))
      else
        if
          ((match sg with | FStarC_Const.Signed -> true | uu___1 -> false) &&
             wide)
            && (v = (Prims.parse_int "-9223372036854775808"))
        then "(-9223372036854775807LL - 1)"
        else
          (let uu___1 = int_suffix sw in
           Prims.strcat (FStarC_Custard_Syntax.c_int_lit_to_string v b)
             uu___1)
let escape (s : Prims.string) : Prims.string=
  let esc c =
    match c with
    | 10 -> "\\n"
    | 9 -> "\\t"
    | 13 -> "\\r"
    | 34 -> "\\\""
    | 92 -> "\\\\"
    | c1 ->
        let i = FStarC_Util.int_of_char c1 in
        if (i < (Prims.of_int 32)) || (i > (Prims.of_int 126))
        then
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int
                ((((i / (Prims.of_int 64)) * (Prims.of_int 100)) +
                    (((mod) (i / (Prims.of_int 8)) (Prims.of_int 8)) *
                       (Prims.of_int 10)))
                   + ((mod) i (Prims.of_int 8))) in
            Prims.strcat
              (if i < (Prims.of_int 8)
               then "00"
               else if i < (Prims.of_int 64) then "0" else "") uu___1 in
          Prims.strcat "\\" uu___
        else FStarC_Util.string_of_char c1 in
  let uu___ = FStarC_List.map esc (FStarC_String.list_of_string s) in
  FStarC_String.concat "" uu___
let narrow_params (fw : FStarC_Custard_Syntax.fwidth) :
  (Prims.int * Prims.int * Prims.int)=
  match fw with
  | FStarC_Custard_Syntax.Float16 ->
      ((Prims.of_int 10), (Prims.of_int (-14)), (Prims.of_int 15))
  | FStarC_Custard_Syntax.BFloat16 ->
      ((Prims.of_int 7), (Prims.of_int (-126)), (Prims.of_int 127))
  | uu___ ->
      FStarC_Effect.failwith "Custard: narrow_params at a wide float width"
let rec pow_int (b : Prims.int) (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else b * (pow_int b (n - Prims.int_one))
let ilog2_rat (num : Prims.int) (den : Prims.int) : Prims.int=
  let rec go e n d fuel =
    if fuel = Prims.int_zero
    then e
    else
      if n >= (d * (Prims.of_int 2))
      then
        go (e + Prims.int_one) n (d * (Prims.of_int 2))
          (fuel - Prims.int_one)
      else
        if n < d
        then
          go (e - Prims.int_one) (n * (Prims.of_int 2)) d
            (fuel - Prims.int_one)
        else e in
  go Prims.int_zero num den (Prims.of_int 4096)
let round_ne (num : Prims.int) (den : Prims.int) : Prims.int=
  let q = num / den in
  let r = num - (q * den) in
  if (r * (Prims.of_int 2)) > den
  then q + Prims.int_one
  else
    if (r * (Prims.of_int 2)) < den
    then q
    else
      if ((mod) q (Prims.of_int 2)) = Prims.int_one
      then q + Prims.int_one
      else q
let narrow_float_bits (fw : FStarC_Custard_Syntax.fwidth)
  (v : FStarC_Custard_Syntax.float_lit) : Prims.int=
  let uu___ = narrow_params fw in
  match uu___ with
  | (p, emin, emax) ->
      let ebits =
        if
          match fw with
          | FStarC_Custard_Syntax.Float16 -> true
          | uu___1 -> false
        then Prims.of_int 5
        else Prims.of_int 8 in
      let sign_bit neg =
        if neg then pow_int (Prims.of_int 2) (p + ebits) else Prims.int_zero in
      (match v with
       | FStarC_Custard_Syntax.FLInf neg ->
           (sign_bit neg) +
             (((pow_int (Prims.of_int 2) ebits) - Prims.int_one) *
                (pow_int (Prims.of_int 2) p))
       | FStarC_Custard_Syntax.FLNan ->
           (((pow_int (Prims.of_int 2) ebits) - Prims.int_one) *
              (pow_int (Prims.of_int 2) p))
             + (pow_int (Prims.of_int 2) (p - Prims.int_one))
       | FStarC_Custard_Syntax.FLNum (neg, mag) ->
           let m = FStarC_Real.mantissa mag in
           let e10 = FStarC_Real.exponent mag in
           let uu___1 =
             if e10 >= Prims.int_zero
             then ((m * (pow_int (Prims.of_int 10) e10)), Prims.int_one)
             else (m, (pow_int (Prims.of_int 10) (- e10))) in
           (match uu___1 with
            | (num, den) ->
                let sign = sign_bit neg in
                if num = Prims.int_zero
                then sign
                else
                  (let e = ilog2_rat num den in
                   let e1 = if e < emin then emin else e in
                   let sh = p - e1 in
                   let uu___2 =
                     if sh >= Prims.int_zero
                     then ((num * (pow_int (Prims.of_int 2) sh)), den)
                     else (num, (den * (pow_int (Prims.of_int 2) (- sh)))) in
                   match uu___2 with
                   | (n2, d2) ->
                       let q = round_ne n2 d2 in
                       let uu___3 =
                         if
                           q >=
                             (pow_int (Prims.of_int 2) (p + Prims.int_one))
                         then ((q / (Prims.of_int 2)), (e1 + Prims.int_one))
                         else (q, e1) in
                       (match uu___3 with
                        | (q1, e2) ->
                            let bias =
                              (pow_int (Prims.of_int 2)
                                 (ebits - Prims.int_one))
                                - Prims.int_one in
                            if e2 > emax
                            then
                              sign +
                                (((pow_int (Prims.of_int 2) ebits) -
                                    Prims.int_one)
                                   * (pow_int (Prims.of_int 2) p))
                            else
                              if q1 < (pow_int (Prims.of_int 2) p)
                              then sign + q1
                              else
                                (sign +
                                   ((e2 + bias) *
                                      (pow_int (Prims.of_int 2) p)))
                                  + (q1 - (pow_int (Prims.of_int 2) p))))))
let narrow_float_lit' (fw : FStarC_Custard_Syntax.fwidth)
  (v : FStarC_Custard_Syntax.float_lit) (sfx : Prims.string) : Prims.string=
  let b = narrow_float_bits fw v in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int b in
          Prims.strcat uu___4 "U)" in
        Prims.strcat "(" uu___3 in
      Prims.strcat sfx uu___2 in
    Prims.strcat
      (if
         match fw with
         | FStarC_Custard_Syntax.Float16 -> true
         | uu___2 -> false
       then "F16"
       else "BF16") uu___1 in
  Prims.strcat "CUSTARD_" uu___
let narrow_float_lit (fw : FStarC_Custard_Syntax.fwidth)
  (v : FStarC_Custard_Syntax.float_lit) : Prims.string=
  narrow_float_lit' fw v "_LIT"
let narrow_float_init (fw : FStarC_Custard_Syntax.fwidth)
  (v : FStarC_Custard_Syntax.float_lit) : Prims.string=
  narrow_float_lit' fw v "_INIT"
let narrow_support : Prims.string=
  FStarC_String.concat "\n"
    ["";
    "#ifndef CUSTARD_FLOAT16_DEFINED";
    "#error \"Custard: this program uses binary16 or bfloat16, which Custard does not implement.  Supply custard_f16/custard_bf16 and their operations in a @@custard_c_header and define CUSTARD_FLOAT16_DEFINED; section 98 of doc/ref/custard.md lists the vocabulary.\"";
    "#endif";
    ""]
let mentions_narrow (s : Prims.string) : Prims.bool=
  (((FStarC_Util.contains s "custard_f16") ||
      (FStarC_Util.contains s "custard_bf16"))
     || (FStarC_Util.contains s "CUSTARD_F16_"))
    || (FStarC_Util.contains s "CUSTARD_BF16_")
let unit_support : Prims.string=
  "#ifndef CUSTARD_UNIT_DEFINED\n#define CUSTARD_UNIT_DEFINED\ntypedef uint8_t custard_unit;\n#endif\n"
let mentions_unit (s : Prims.string) : Prims.bool=
  FStarC_Util.contains s "custard_unit"
let float_special_support : Prims.string=
  "#ifndef CUSTARD_FLOAT_SPECIAL_DEFINED\n#define CUSTARD_FLOAT_SPECIAL_DEFINED\n#include <math.h>\n#define CUSTARD_NAN NAN\n#define CUSTARD_INF INFINITY\n#endif\n"
let mentions_float_special (s : Prims.string) : Prims.bool=
  (FStarC_Util.contains s "CUSTARD_NAN") ||
    (FStarC_Util.contains s "CUSTARD_INF")
let constant (c : FStarC_Custard_Syntax.constant) : Prims.string=
  match c with
  | FStarC_Custard_Syntax.CUnit -> unit_value
  | FStarC_Custard_Syntax.CBool b -> if b then "true" else "false"
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.Some sw) ->
      if (FStar_Pervasives_Native.snd sw) = FStarC_Custard_Syntax.W128
      then int_literal sw v b
      else
        (let uu___ =
           let uu___1 = int_type sw in
           let uu___2 =
             let uu___3 =
               let uu___4 = int_literal sw v b in Prims.strcat uu___4 ")" in
             Prims.strcat ")" uu___3 in
           Prims.strcat uu___1 uu___2 in
         Prims.strcat "((" uu___)
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.None) ->
      reject
        (Prims.strcat "the unbounded integer literal "
           (FStarC_Custard_Syntax.int_lit_to_string v b))
        ["Prims.int has no C representation; use a machine integer type."]
  | FStarC_Custard_Syntax.CFloat (FStarC_Custard_Syntax.FLNan, fw) when
      (match fw with | FStarC_Custard_Syntax.Float32 -> true | uu___ -> false)
        ||
        (match fw with
         | FStarC_Custard_Syntax.Float64 -> true
         | uu___ -> false)
      -> "CUSTARD_NAN"
  | FStarC_Custard_Syntax.CFloat (FStarC_Custard_Syntax.FLInf neg, fw) when
      (match fw with | FStarC_Custard_Syntax.Float32 -> true | uu___ -> false)
        ||
        (match fw with
         | FStarC_Custard_Syntax.Float64 -> true
         | uu___ -> false)
      -> if neg then "(-CUSTARD_INF)" else "CUSTARD_INF"
  | FStarC_Custard_Syntax.CFloat (v, FStarC_Custard_Syntax.Float32) ->
      Prims.strcat (FStarC_Custard_Syntax.float_lit_to_string v) "f"
  | FStarC_Custard_Syntax.CFloat (v, FStarC_Custard_Syntax.Float64) ->
      FStarC_Custard_Syntax.float_lit_to_string v
  | FStarC_Custard_Syntax.CFloat (v, fw) -> narrow_float_lit fw v
  | FStarC_Custard_Syntax.CChar c1 ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            (FStarC_Util.int_of_char c1) in
        Prims.strcat uu___1 ")" in
      Prims.strcat "((uint32_t)" uu___
  | FStarC_Custard_Syntax.CString s ->
      let uu___ = let uu___1 = escape s in Prims.strcat uu___1 "\"" in
      Prims.strcat "\"" uu___
let converted_int (target : FStarC_Custard_Syntax.cty)
  (e_ty : FStarC_Custard_Syntax.cty) (c : FStarC_Custard_Syntax.constant) :
  Prims.string FStar_Pervasives_Native.option=
  match c with
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.Some sw) when
      (target = e_ty) && (e_ty = (FStarC_Custard_Syntax.TInt sw)) ->
      if ((Prims.of_int (-32767)) <= v) && (v <= (Prims.of_int 32767))
      then
        FStar_Pervasives_Native.Some
          (FStarC_Custard_Syntax.c_int_lit_to_string v b)
      else
        (let uu___ = int_literal sw v b in FStar_Pervasives_Native.Some uu___)
  | FStarC_Custard_Syntax.CChar c1 when
      (target = e_ty) &&
        ((FStarC_Util.int_of_char c1) <= (Prims.of_int 32767))
      ->
      let uu___ =
        FStarC_Class_Show.show FStarC_Class_Show.showable_int
          (FStarC_Util.int_of_char c1) in
      FStar_Pervasives_Native.Some uu___
  | uu___ -> FStar_Pervasives_Native.None
let infix_op (o : FStarC_Custard_Syntax.prim_op) :
  Prims.string FStar_Pervasives_Native.option=
  match o.FStarC_Custard_Syntax.po_op with
  | FStarC_Custard_Syntax.Add -> FStar_Pervasives_Native.Some "+"
  | FStarC_Custard_Syntax.AddW -> FStar_Pervasives_Native.Some "+"
  | FStarC_Custard_Syntax.Sub -> FStar_Pervasives_Native.Some "-"
  | FStarC_Custard_Syntax.SubW -> FStar_Pervasives_Native.Some "-"
  | FStarC_Custard_Syntax.Mult -> FStar_Pervasives_Native.Some "*"
  | FStarC_Custard_Syntax.MultW -> FStar_Pervasives_Native.Some "*"
  | FStarC_Custard_Syntax.Div -> FStar_Pervasives_Native.Some "/"
  | FStarC_Custard_Syntax.DivW -> FStar_Pervasives_Native.Some "/"
  | FStarC_Custard_Syntax.Mod -> FStar_Pervasives_Native.Some "%"
  | FStarC_Custard_Syntax.BOr -> FStar_Pervasives_Native.Some "|"
  | FStarC_Custard_Syntax.BAnd -> FStar_Pervasives_Native.Some "&"
  | FStarC_Custard_Syntax.BXor -> FStar_Pervasives_Native.Some "^"
  | FStarC_Custard_Syntax.BShiftL -> FStar_Pervasives_Native.Some "<<"
  | FStarC_Custard_Syntax.BShiftR -> FStar_Pervasives_Native.Some ">>"
  | FStarC_Custard_Syntax.Eq -> FStar_Pervasives_Native.Some "=="
  | FStarC_Custard_Syntax.Neq -> FStar_Pervasives_Native.Some "!="
  | FStarC_Custard_Syntax.Lt -> FStar_Pervasives_Native.Some "<"
  | FStarC_Custard_Syntax.Lte -> FStar_Pervasives_Native.Some "<="
  | FStarC_Custard_Syntax.Gt -> FStar_Pervasives_Native.Some ">"
  | FStarC_Custard_Syntax.Gte -> FStar_Pervasives_Native.Some ">="
  | FStarC_Custard_Syntax.And ->
      FStar_Pervasives_Native.Some
        (if FStarC_Custard_Syntax.at_int_width o then "&" else "&&")
  | FStarC_Custard_Syntax.Or ->
      FStar_Pervasives_Native.Some
        (if FStarC_Custard_Syntax.at_int_width o then "|" else "||")
  | uu___ -> FStar_Pervasives_Native.None
let prefix_op (o : FStarC_Custard_Syntax.prim_op) :
  Prims.string FStar_Pervasives_Native.option=
  match o.FStarC_Custard_Syntax.po_op with
  | FStarC_Custard_Syntax.Not ->
      FStar_Pervasives_Native.Some
        (if FStarC_Custard_Syntax.at_int_width o then "~" else "!")
  | FStarC_Custard_Syntax.BNot -> FStar_Pervasives_Native.Some "~"
  | uu___ -> FStar_Pervasives_Native.None
let narrow_ty (fw : FStarC_Custard_Syntax.fwidth) : Prims.bool=
  (match fw with | FStarC_Custard_Syntax.Float16 -> true | uu___ -> false) ||
    (match fw with | FStarC_Custard_Syntax.BFloat16 -> true | uu___ -> false)
let narrow_pfx (fw : FStarC_Custard_Syntax.fwidth) : Prims.string=
  if match fw with | FStarC_Custard_Syntax.Float16 -> true | uu___ -> false
  then "custard_f16_"
  else "custard_bf16_"
let narrow_fw (o : FStarC_Custard_Syntax.prim_op) :
  FStarC_Custard_Syntax.fwidth FStar_Pervasives_Native.option=
  match o.FStarC_Custard_Syntax.po_ty with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
      (FStarC_Custard_Syntax.Float16)) ->
      FStar_Pervasives_Native.Some FStarC_Custard_Syntax.Float16
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat
      (FStarC_Custard_Syntax.BFloat16)) ->
      FStar_Pervasives_Native.Some FStarC_Custard_Syntax.BFloat16
  | uu___ -> FStar_Pervasives_Native.None
let narrow_call (o : FStarC_Custard_Syntax.prim_op) :
  Prims.string FStar_Pervasives_Native.option=
  match narrow_fw o with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some fw ->
      let pfx =
        if
          match fw with
          | FStarC_Custard_Syntax.Float16 -> true
          | uu___ -> false
        then "custard_f16_"
        else "custard_bf16_" in
      (match o.FStarC_Custard_Syntax.po_op with
       | FStarC_Custard_Syntax.Add ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "add")
       | FStarC_Custard_Syntax.AddW ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "add")
       | FStarC_Custard_Syntax.Sub ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "sub")
       | FStarC_Custard_Syntax.SubW ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "sub")
       | FStarC_Custard_Syntax.Mult ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "mul")
       | FStarC_Custard_Syntax.MultW ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "mul")
       | FStarC_Custard_Syntax.Div ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "div")
       | FStarC_Custard_Syntax.DivW ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "div")
       | FStarC_Custard_Syntax.Eq ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "eq")
       | FStarC_Custard_Syntax.Neq ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "neq")
       | FStarC_Custard_Syntax.Lt ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "lt")
       | FStarC_Custard_Syntax.Lte ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "lte")
       | FStarC_Custard_Syntax.Gt ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "gt")
       | FStarC_Custard_Syntax.Gte ->
           FStar_Pervasives_Native.Some (Prims.strcat pfx "gte")
       | uu___ -> FStar_Pervasives_Native.None)
let truncate (o : FStarC_Custard_Syntax.prim_op) (s : Prims.string) :
  Prims.string=
  let modular =
    match o.FStarC_Custard_Syntax.po_op with
    | FStarC_Custard_Syntax.Not -> FStarC_Custard_Syntax.at_int_width o
    | FStarC_Custard_Syntax.BNot -> true
    | FStarC_Custard_Syntax.BShiftL -> true
    | FStarC_Custard_Syntax.AddW -> true
    | FStarC_Custard_Syntax.SubW -> true
    | FStarC_Custard_Syntax.MultW -> true
    | uu___ -> false in
  match o.FStarC_Custard_Syntax.po_ty with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw) ->
      let uu___ = sw in
      (match uu___ with
       | (uu___1, w) ->
           let narrow =
             match w with
             | FStarC_Custard_Syntax.W8 -> true
             | FStarC_Custard_Syntax.W16 -> true
             | uu___2 -> false in
           if modular && narrow
           then
             let uu___2 =
               let uu___3 = int_type sw in
               Prims.strcat uu___3 (Prims.strcat ")" (Prims.strcat s ")")) in
             Prims.strcat "((" uu___2
           else s)
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat uu___) -> s
  | FStar_Pervasives_Native.None -> s
let widen_operands (o : FStarC_Custard_Syntax.prim_op) :
  Prims.string FStar_Pervasives_Native.option=
  let wrapping =
    match o.FStarC_Custard_Syntax.po_op with
    | FStarC_Custard_Syntax.AddW -> true
    | FStarC_Custard_Syntax.SubW -> true
    | FStarC_Custard_Syntax.MultW -> true
    | FStarC_Custard_Syntax.BShiftL -> true
    | uu___ -> false in
  match o.FStarC_Custard_Syntax.po_ty with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt
      (FStarC_Const.Unsigned, w)) when wrapping ->
      (match w with
       | FStarC_Custard_Syntax.W8 ->
           FStar_Pervasives_Native.Some "(unsigned int)"
       | FStarC_Custard_Syntax.W16 ->
           FStar_Pervasives_Native.Some "(unsigned int)"
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
type dest =
  | D_Return 
  | D_Assign of Prims.string 
  | D_Ignore 
let uu___is_D_Return (projectee : dest) : Prims.bool=
  match projectee with | D_Return -> true | uu___ -> false
let uu___is_D_Assign (projectee : dest) : Prims.bool=
  match projectee with | D_Assign _0 -> true | uu___ -> false
let __proj__D_Assign__item___0 (projectee : dest) : Prims.string=
  match projectee with | D_Assign _0 -> _0
let uu___is_D_Ignore (projectee : dest) : Prims.bool=
  match projectee with | D_Ignore -> true | uu___ -> false
let scope :
  (Prims.string * (Prims.string * Prims.bool)) Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let declared : Prims.bool FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let reset_scope (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals scope [];
  (let uu___2 = FStarC_SMap.create (Prims.of_int 20) in
   FStarC_Effect.op_Colon_Equals declared uu___2)
let bind_gen (x : Prims.string) (cell : Prims.bool) : Prims.string=
  let base = c_var x in
  let rec pick i =
    let cand =
      if i = Prims.int_zero
      then base
      else
        (let uu___ =
           let uu___1 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
           Prims.strcat "_" uu___1 in
         Prims.strcat base uu___) in
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang declared in
        FStarC_SMap.try_find uu___2 cand in
      match uu___1 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___2 -> false in
    if uu___ then pick (i + Prims.int_one) else cand in
  let nm = pick Prims.int_zero in
  (let uu___1 = FStarC_Effect.op_Bang declared in
   FStarC_SMap.add uu___1 nm true);
  (let uu___2 =
     let uu___3 = FStarC_Effect.op_Bang scope in (x, (nm, cell)) :: uu___3 in
   FStarC_Effect.op_Colon_Equals scope uu___2);
  nm
let bind_var (x : Prims.string) : Prims.string= bind_gen x false
let bind_cell (x : Prims.string) : Prims.string= bind_gen x true
let bind_alias (x : Prims.string) (path : Prims.string) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang scope in (x, (path, false)) :: uu___1 in
  FStarC_Effect.op_Colon_Equals scope uu___
let lookup_var (x : Prims.string) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang scope in
    FStarC_List.tryFind
      (fun uu___2 -> match uu___2 with | (y, uu___3) -> y = x) uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, (nm, uu___2)) -> nm
  | FStar_Pervasives_Native.None ->
      reject_ir (Prims.strcat "the unbound variable " x)
        ["No binder in this definition introduces it.";
        "This is a compiler bug: please report it, with the definition named above."]
let is_cell (x : Prims.string) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang scope in
    FStarC_List.tryFind
      (fun uu___2 -> match uu___2 with | (y, uu___3) -> y = x) uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___1, (uu___2, c)) -> c
  | FStar_Pervasives_Native.None -> false
let ctr : Prims.int FStarC_Effect.ref= FStarC_Effect.mk_ref Prims.int_zero
let fresh (stem : Prims.string) : Prims.string=
  (let uu___1 =
     let uu___2 = FStarC_Effect.op_Bang ctr in uu___2 + Prims.int_one in
   FStarC_Effect.op_Colon_Equals ctr uu___1);
  (let nm =
     let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_Effect.op_Bang ctr in
         FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3 in
       Prims.strcat stem uu___2 in
     Prims.strcat "_c" uu___1 in
   (let uu___2 = FStarC_Effect.op_Bang declared in
    FStarC_SMap.add uu___2 nm true);
   nm)
let reset_program_state (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals current "<toplevel>";
  FStarC_SMap.clear parents;
  FStarC_SMap.clear frozen_by;
  FStarC_SMap.clear frozen_by_target;
  FStarC_SMap.clear existentials;
  FStarC_SMap.clear root_decls;
  (let uu___8 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals renames uu___8);
  (let uu___9 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals macros uu___9);
  (let uu___10 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals types uu___10);
  (let uu___11 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals ctors uu___11);
  (let uu___12 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals externs uu___12);
  (let uu___13 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals keeps uu___13);
  (let uu___14 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals void_fns uu___14);
  (let uu___15 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals arities uu___15);
  FStarC_Effect.op_Colon_Equals void_ret false;
  FStarC_Effect.op_Colon_Equals eq_queue [];
  (let uu___18 = FStarC_SMap.create (Prims.of_int 20) in
   FStarC_Effect.op_Colon_Equals eq_seen uu___18);
  (let uu___19 = FStarC_SMap.create (Prims.of_int 50) in
   FStarC_Effect.op_Colon_Equals taken_names uu___19);
  FStarC_Effect.op_Colon_Equals scope [];
  (let uu___21 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals declared uu___21);
  FStarC_Effect.op_Colon_Equals ctr Prims.int_zero
let is_stmt (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet uu___ -> true
  | FStarC_Custard_Syntax.EMatch uu___ -> true
  | FStarC_Custard_Syntax.EIf uu___ -> true
  | FStarC_Custard_Syntax.ESeq uu___ -> true
  | FStarC_Custard_Syntax.EWhile uu___ -> true
  | FStarC_Custard_Syntax.EAbort uu___ -> true
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate uu___;
         FStarC_Custard_Syntax.po_ty = uu___1;_},
       uu___2)
      -> true
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> true
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufBlit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> true
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufFree;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> true
  | uu___ -> false
let rec vars_of (e : FStarC_Custard_Syntax.expr) : Prims.string Prims.list=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar x -> [x]
  | FStarC_Custard_Syntax.EConst uu___ -> []
  | FStarC_Custard_Syntax.EQual uu___ -> []
  | FStarC_Custard_Syntax.EAny -> []
  | FStarC_Custard_Syntax.EAbort uu___ -> []
  | FStarC_Custard_Syntax.ELet (uu___, uu___1, a, b) ->
      let uu___2 = vars_of a in
      let uu___3 = vars_of b in FStarC_List.op_At uu___2 uu___3
  | FStarC_Custard_Syntax.EApp (h, es) ->
      let uu___ = vars_of h in
      let uu___1 = FStarC_List.collect vars_of es in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.EFun (uu___, b) -> vars_of b
  | FStarC_Custard_Syntax.EMatch (sc, brs) ->
      let uu___ = vars_of sc in
      let uu___1 = FStarC_List.collect vars_of_branch brs in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.ETry (a, brs) ->
      let uu___ = vars_of a in
      let uu___1 = FStarC_List.collect vars_of_branch brs in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.EIf (a, b, c) ->
      let uu___ = vars_of a in
      let uu___1 =
        let uu___2 = vars_of b in
        let uu___3 = vars_of c in FStarC_List.op_At uu___2 uu___3 in
      FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.ESeq (a, b) ->
      let uu___ = vars_of a in
      let uu___1 = vars_of b in FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.EWhile (a, b) ->
      let uu___ = vars_of a in
      let uu___1 = vars_of b in FStarC_List.op_At uu___ uu___1
  | FStarC_Custard_Syntax.ECtor (uu___, es) -> FStarC_List.collect vars_of es
  | FStarC_Custard_Syntax.ETuple es -> FStarC_List.collect vars_of es
  | FStarC_Custard_Syntax.EOp (uu___, es) -> FStarC_List.collect vars_of es
  | FStarC_Custard_Syntax.ERaise e1 -> vars_of e1
  | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
      FStarC_List.collect
        (fun uu___1 -> match uu___1 with | (uu___2, e1) -> vars_of e1) fs
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> vars_of a
  | FStarC_Custard_Syntax.EDiscrim (a, uu___) -> vars_of a
  | FStarC_Custard_Syntax.ECast (a, uu___) -> vars_of a
  | FStarC_Custard_Syntax.ECoerce (a, uu___) -> vars_of a
and vars_of_branch (br : FStarC_Custard_Syntax.branch) :
  Prims.string Prims.list=
  let uu___ = br in
  match uu___ with
  | (uu___1, g, b) ->
      let uu___2 =
        match g with
        | FStar_Pervasives_Native.Some g1 -> vars_of g1
        | FStar_Pervasives_Native.None -> [] in
      let uu___3 = vars_of b in FStarC_List.op_At uu___2 uu___3
let rec mutates (x : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  let any es = FStarC_List.existsb (mutates x) es in
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar y -> y = x
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       { FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EVar y;
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_}::i::[])
      when y = x -> mutates x i
  | FStarC_Custard_Syntax.EConst uu___ -> false
  | FStarC_Custard_Syntax.EQual uu___ -> false
  | FStarC_Custard_Syntax.EAny -> false
  | FStarC_Custard_Syntax.EAbort uu___ -> false
  | FStarC_Custard_Syntax.ELet (uu___, uu___1, a, b) ->
      let uu___2 = mutates x a in if uu___2 then true else mutates x b
  | FStarC_Custard_Syntax.EApp (h, es) ->
      let uu___ = mutates x h in if uu___ then true else any es
  | FStarC_Custard_Syntax.EFun (uu___, b) -> mutates x b
  | FStarC_Custard_Syntax.EMatch (sc, brs) ->
      let uu___ = mutates x sc in
      if uu___ then true else FStarC_List.existsb (mutates_branch x) brs
  | FStarC_Custard_Syntax.ETry (a, brs) ->
      let uu___ = mutates x a in
      if uu___ then true else FStarC_List.existsb (mutates_branch x) brs
  | FStarC_Custard_Syntax.EIf (a, b, c) ->
      let uu___ =
        let uu___1 = mutates x a in if uu___1 then true else mutates x b in
      if uu___ then true else mutates x c
  | FStarC_Custard_Syntax.ESeq (a, b) ->
      let uu___ = mutates x a in if uu___ then true else mutates x b
  | FStarC_Custard_Syntax.EWhile (a, b) ->
      let uu___ = mutates x a in if uu___ then true else mutates x b
  | FStarC_Custard_Syntax.ECtor (uu___, es) -> any es
  | FStarC_Custard_Syntax.ETuple es -> any es
  | FStarC_Custard_Syntax.EOp (uu___, es) -> any es
  | FStarC_Custard_Syntax.ERaise e1 -> mutates x e1
  | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
      FStarC_List.existsb
        (fun uu___1 -> match uu___1 with | (uu___2, e1) -> mutates x e1) fs
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> mutates x a
  | FStarC_Custard_Syntax.EDiscrim (a, uu___) -> mutates x a
  | FStarC_Custard_Syntax.ECast (a, uu___) -> mutates x a
  | FStarC_Custard_Syntax.ECoerce (a, uu___) -> mutates x a
and mutates_branch (x : Prims.string) (br : FStarC_Custard_Syntax.branch) :
  Prims.bool=
  let uu___ = br in
  match uu___ with
  | (uu___1, g, b) ->
      let uu___2 =
        match g with
        | FStar_Pervasives_Native.Some g1 -> mutates x g1
        | FStar_Pervasives_Native.None -> false in
      if uu___2 then true else mutates x b
let rec is_stable (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar x -> let uu___ = is_cell x in Prims.not uu___
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> is_stable a
  | uu___ -> false
let rec is_lvalue (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar uu___ -> true
  | FStarC_Custard_Syntax.EQual uu___ -> true
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1::uu___2::[])
      -> true
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> is_lvalue a
  | uu___ -> false
let rec is_pure (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  let all es = FStarC_List.for_all is_pure es in
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst uu___ -> true
  | FStarC_Custard_Syntax.EVar uu___ -> true
  | FStarC_Custard_Syntax.EQual uu___ -> true
  | FStarC_Custard_Syntax.EAny -> true
  | FStarC_Custard_Syntax.EApp uu___ -> false
  | FStarC_Custard_Syntax.EFun uu___ -> false
  | FStarC_Custard_Syntax.EWhile uu___ -> false
  | FStarC_Custard_Syntax.EAbort uu___ -> false
  | FStarC_Custard_Syntax.ERaise uu___ -> false
  | FStarC_Custard_Syntax.ETry uu___ -> false
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       es)
      -> all es
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate uu___;
         FStarC_Custard_Syntax.po_ty = uu___1;_},
       uu___2)
      -> false
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> false
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufFree;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> false
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufBlit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> false
  | FStarC_Custard_Syntax.EOp (uu___, es) -> all es
  | FStarC_Custard_Syntax.ECtor (uu___, es) -> all es
  | FStarC_Custard_Syntax.ETuple es -> all es
  | FStarC_Custard_Syntax.ELet (uu___, uu___1, a, b) ->
      let uu___2 = is_pure a in if uu___2 then is_pure b else false
  | FStarC_Custard_Syntax.ESeq (a, b) ->
      let uu___ = is_pure a in if uu___ then is_pure b else false
  | FStarC_Custard_Syntax.EIf (a, b, c) ->
      let uu___ =
        let uu___1 = is_pure a in if uu___1 then is_pure b else false in
      if uu___ then is_pure c else false
  | FStarC_Custard_Syntax.EMatch (sc, brs) ->
      let uu___ = is_pure sc in
      if uu___ then FStarC_List.for_all is_pure_branch brs else false
  | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
      FStarC_List.for_all
        (fun uu___1 -> match uu___1 with | (uu___2, e1) -> is_pure e1) fs
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> is_pure a
  | FStarC_Custard_Syntax.EDiscrim (a, uu___) -> is_pure a
  | FStarC_Custard_Syntax.ECast (a, uu___) -> is_pure a
  | FStarC_Custard_Syntax.ECoerce (a, uu___) -> is_pure a
and is_pure_branch (br : FStarC_Custard_Syntax.branch) : Prims.bool=
  let uu___ = br in
  match uu___ with
  | (uu___1, g, b) ->
      let uu___2 =
        match g with
        | FStar_Pervasives_Native.Some g1 -> is_pure g1
        | FStar_Pervasives_Native.None -> true in
      if uu___2 then is_pure b else false
let rec cell_dead (x : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.bool=
  let all es = FStarC_List.for_all (cell_dead x) es in
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EVar y -> y <> x
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       { FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EVar y;
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_}::i::v::[])
      when y = x ->
      let uu___3 = FStarC_Custard_Syntax.is_droppable i in
      if uu___3 then FStarC_Custard_Syntax.is_droppable v else false
  | FStarC_Custard_Syntax.EConst uu___ -> true
  | FStarC_Custard_Syntax.EQual uu___ -> true
  | FStarC_Custard_Syntax.EAny -> true
  | FStarC_Custard_Syntax.EAbort uu___ -> true
  | FStarC_Custard_Syntax.ELet (uu___, uu___1, a, b) ->
      let uu___2 = cell_dead x a in if uu___2 then cell_dead x b else false
  | FStarC_Custard_Syntax.ESeq (a, b) ->
      let uu___ = cell_dead x a in if uu___ then cell_dead x b else false
  | FStarC_Custard_Syntax.EWhile (a, b) ->
      let uu___ = cell_dead x a in if uu___ then cell_dead x b else false
  | FStarC_Custard_Syntax.EApp (h, es) ->
      let uu___ = cell_dead x h in if uu___ then all es else false
  | FStarC_Custard_Syntax.EFun (uu___, b) -> cell_dead x b
  | FStarC_Custard_Syntax.ERaise b -> cell_dead x b
  | FStarC_Custard_Syntax.EMatch (sc, brs) ->
      let uu___ = cell_dead x sc in
      if uu___ then FStarC_List.for_all (cell_dead_branch x) brs else false
  | FStarC_Custard_Syntax.ETry (a, brs) ->
      let uu___ = cell_dead x a in
      if uu___ then FStarC_List.for_all (cell_dead_branch x) brs else false
  | FStarC_Custard_Syntax.EIf (a, b, c) ->
      let uu___ =
        let uu___1 = cell_dead x a in if uu___1 then cell_dead x b else false in
      if uu___ then cell_dead x c else false
  | FStarC_Custard_Syntax.ECtor (uu___, es) -> all es
  | FStarC_Custard_Syntax.ETuple es -> all es
  | FStarC_Custard_Syntax.EOp (uu___, es) -> all es
  | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
      FStarC_List.for_all
        (fun uu___1 -> match uu___1 with | (uu___2, e1) -> cell_dead x e1) fs
  | FStarC_Custard_Syntax.EProj (a, uu___, uu___1) -> cell_dead x a
  | FStarC_Custard_Syntax.EDiscrim (a, uu___) -> cell_dead x a
  | FStarC_Custard_Syntax.ECast (a, uu___) -> cell_dead x a
  | FStarC_Custard_Syntax.ECoerce (a, uu___) -> cell_dead x a
and cell_dead_branch (x : Prims.string) (br : FStarC_Custard_Syntax.branch) :
  Prims.bool=
  let uu___ = br in
  match uu___ with
  | (uu___1, g, b) ->
      let uu___2 =
        match g with
        | FStar_Pervasives_Native.Some g1 -> cell_dead x g1
        | FStar_Pervasives_Native.None -> true in
      if uu___2 then cell_dead x b else false
let rec drop_writes (x : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  FStarC_Custard_Syntax.expr=
  let go e1 = drop_writes x e1 in
  let go_branch br =
    let uu___ = br in
    match uu___ with
    | (p, g, b) ->
        let uu___1 =
          match g with
          | FStar_Pervasives_Native.Some g1 ->
              let uu___2 = go g1 in FStar_Pervasives_Native.Some uu___2
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        let uu___2 = go b in (p, uu___1, uu___2) in
  let e' =
    match e.FStarC_Custard_Syntax.e with
    | FStarC_Custard_Syntax.EOp
        ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
           FStarC_Custard_Syntax.po_ty = uu___;_},
         { FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EVar y;
           FStarC_Custard_Syntax.ty = uu___1;
           FStarC_Custard_Syntax.eff = uu___2;_}::uu___3::uu___4::[])
        when y = x ->
        FStarC_Custard_Syntax.EConst FStarC_Custard_Syntax.CUnit
    | FStarC_Custard_Syntax.EConst uu___ -> e.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EVar uu___ -> e.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EQual uu___ -> e.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EAny -> e.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.EAbort uu___ -> e.FStarC_Custard_Syntax.e
    | FStarC_Custard_Syntax.ELet (n, t, a, b) ->
        let uu___ =
          let uu___1 = go a in let uu___2 = go b in (n, t, uu___1, uu___2) in
        FStarC_Custard_Syntax.ELet uu___
    | FStarC_Custard_Syntax.ESeq (a, b) ->
        let uu___ =
          let uu___1 = go a in let uu___2 = go b in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ESeq uu___
    | FStarC_Custard_Syntax.EWhile (a, b) ->
        let uu___ =
          let uu___1 = go a in let uu___2 = go b in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EWhile uu___
    | FStarC_Custard_Syntax.EApp (h, es) ->
        let uu___ =
          let uu___1 = go h in
          let uu___2 = FStarC_List.map go es in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EApp uu___
    | FStarC_Custard_Syntax.EFun (bs, b) ->
        let uu___ = let uu___1 = go b in (bs, uu___1) in
        FStarC_Custard_Syntax.EFun uu___
    | FStarC_Custard_Syntax.ERaise a ->
        let uu___ = go a in FStarC_Custard_Syntax.ERaise uu___
    | FStarC_Custard_Syntax.EMatch (sc, brs) ->
        let uu___ =
          let uu___1 = go sc in
          let uu___2 = FStarC_List.map go_branch brs in (uu___1, uu___2) in
        FStarC_Custard_Syntax.EMatch uu___
    | FStarC_Custard_Syntax.ETry (a, brs) ->
        let uu___ =
          let uu___1 = go a in
          let uu___2 = FStarC_List.map go_branch brs in (uu___1, uu___2) in
        FStarC_Custard_Syntax.ETry uu___
    | FStarC_Custard_Syntax.EIf (a, b, c) ->
        let uu___ =
          let uu___1 = go a in
          let uu___2 = go b in let uu___3 = go c in (uu___1, uu___2, uu___3) in
        FStarC_Custard_Syntax.EIf uu___
    | FStarC_Custard_Syntax.ECtor (n, es) ->
        let uu___ = let uu___1 = FStarC_List.map go es in (n, uu___1) in
        FStarC_Custard_Syntax.ECtor uu___
    | FStarC_Custard_Syntax.ETuple es ->
        let uu___ = FStarC_List.map go es in
        FStarC_Custard_Syntax.ETuple uu___
    | FStarC_Custard_Syntax.EOp (o, es) ->
        let uu___ = let uu___1 = FStarC_List.map go es in (o, uu___1) in
        FStarC_Custard_Syntax.EOp uu___
    | FStarC_Custard_Syntax.ERecord (n, fs) ->
        let uu___ =
          let uu___1 =
            FStarC_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (f, e1) -> let uu___3 = go e1 in (f, uu___3)) fs in
          (n, uu___1) in
        FStarC_Custard_Syntax.ERecord uu___
    | FStarC_Custard_Syntax.EProj (a, n, f) ->
        let uu___ = let uu___1 = go a in (uu___1, n, f) in
        FStarC_Custard_Syntax.EProj uu___
    | FStarC_Custard_Syntax.EDiscrim (a, n) ->
        let uu___ = let uu___1 = go a in (uu___1, n) in
        FStarC_Custard_Syntax.EDiscrim uu___
    | FStarC_Custard_Syntax.ECast (a, t) ->
        let uu___ = let uu___1 = go a in (uu___1, t) in
        FStarC_Custard_Syntax.ECast uu___
    | FStarC_Custard_Syntax.ECoerce (a, t) ->
        let uu___ = let uu___1 = go a in (uu___1, t) in
        FStarC_Custard_Syntax.ECoerce uu___ in
  {
    FStarC_Custard_Syntax.e = e';
    FStarC_Custard_Syntax.ty = (e.FStarC_Custard_Syntax.ty);
    FStarC_Custard_Syntax.eff = (e.FStarC_Custard_Syntax.eff)
  }
let init_list_max : Prims.int= Prims.of_int 64
let is_one (e : FStarC_Custard_Syntax.expr) : Prims.bool=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt
      (uu___, uu___1, uu___2)) when uu___ = Prims.int_one -> true
  | uu___ -> false
let rec zip_fields
  (fs : (Prims.string * FStarC_Custard_Syntax.cty) Prims.list)
  (vs : Prims.string Prims.list) : (Prims.string * Prims.string) Prims.list=
  match (fs, vs) with
  | ((f, uu___)::fs1, v::vs1) -> (f, v) :: (zip_fields fs1 vs1)
  | uu___ -> []
let rec c_expr (out : Prims.string FStarC_Effect.ref) (ind : Prims.string)
  (e : FStarC_Custard_Syntax.expr) : Prims.string=
  if is_stmt e
  then hoist out ind e
  else
    (match e.FStarC_Custard_Syntax.e with
     | FStarC_Custard_Syntax.EConst c -> constant c
     | FStarC_Custard_Syntax.EVar x ->
         let uu___ = is_cell x in
         if uu___
         then let uu___1 = lookup_var x in Prims.strcat "&" uu___1
         else lookup_var x
     | FStarC_Custard_Syntax.EAny ->
         let uu___ =
           let uu___1 = ty e.FStarC_Custard_Syntax.ty in
           Prims.strcat uu___1 "){0}" in
         Prims.strcat "(" uu___
     | FStarC_Custard_Syntax.EQual (n, uu___) ->
         let uu___1 =
           let uu___2 = FStarC_Effect.op_Bang externs in
           let uu___3 = FStarC_Custard_Syntax.string_of_name n in
           FStarC_SMap.try_find uu___2 uu___3 in
         (match uu___1 with
          | FStar_Pervasives_Native.Some t -> t
          | FStar_Pervasives_Native.None -> c_name n)
     | FStarC_Custard_Syntax.EApp (hd, args) ->
         let args1 =
           match hd.FStarC_Custard_Syntax.e with
           | FStarC_Custard_Syntax.EQual (n, uu___) ->
               let uu___1 =
                 let uu___2 = FStarC_Effect.op_Bang keeps in
                 let uu___3 = FStarC_Custard_Syntax.string_of_name n in
                 FStarC_SMap.try_find uu___2 uu___3 in
               (match uu___1 with
                | FStar_Pervasives_Native.Some flags -> filter_by flags args
                | FStar_Pervasives_Native.None -> args)
           | uu___ ->
               FStarC_List.filter
                 (fun a ->
                    Prims.not
                      (match a.FStarC_Custard_Syntax.ty with
                       | FStarC_Custard_Syntax.TUnit -> true
                       | uu___1 -> false)) args in
         ((match hd.FStarC_Custard_Syntax.e with
           | FStarC_Custard_Syntax.EQual (n, uu___1) ->
               let uu___2 =
                 let uu___3 = FStarC_Effect.op_Bang arities in
                 let uu___4 = FStarC_Custard_Syntax.string_of_name n in
                 FStarC_SMap.try_find uu___3 uu___4 in
               (match uu___2 with
                | FStar_Pervasives_Native.Some a when
                    a <> (FStarC_List.length args1) ->
                    let got = Prims.string_of_int (FStarC_List.length args1) in
                    let want = Prims.string_of_int a in
                    if (FStarC_List.length args1) < a
                    then
                      let uu___3 =
                        let uu___4 = FStarC_Custard_Syntax.string_of_name n in
                        Prims.strcat "the partial application of " uu___4 in
                      reject uu___3
                        [Prims.strcat "It is applied to "
                           (Prims.strcat got
                              (Prims.strcat " of its "
                                 (Prims.strcat want " arguments.")));
                        "The result is a closure over the arguments it did get, and C has no closures.";
                        "A top-level definition is eta-expanded to full arity automatically (section 25), so this is either a local partial application -- name it as a top-level function taking every argument -- or a definition whose body is too costly to re-evaluate at each call (section 25.3)."]
                    else
                      (let uu___3 =
                         let uu___4 = FStarC_Custard_Syntax.string_of_name n in
                         Prims.strcat "an over-application of " uu___4 in
                       reject_ir uu___3
                         [Prims.strcat "It takes "
                            (Prims.strcat want
                               (Prims.strcat " arguments and is applied to "
                                  (Prims.strcat got ".")));
                         "Applying a call's result is a separate application node."])
                | uu___3 -> ())
           | uu___1 -> ());
          (let cast_free_args =
             match hd.FStarC_Custard_Syntax.e with
             | FStarC_Custard_Syntax.EQual (n, uu___1) ->
                 let uu___2 =
                   let uu___3 = FStarC_Effect.op_Bang externs in
                   let uu___4 = FStarC_Custard_Syntax.string_of_name n in
                   FStarC_SMap.try_find uu___3 uu___4 in
                 (match uu___2 with
                  | FStar_Pervasives_Native.None -> true
                  | uu___3 -> false)
             | uu___1 -> true in
           let call =
             let uu___1 = c_expr out ind hd in
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     FStarC_List.map
                       (fun a ->
                          if cast_free_args
                          then c_rvalue out ind a.FStarC_Custard_Syntax.ty a
                          else c_expr out ind a) args1 in
                   FStarC_String.concat ", " uu___5 in
                 Prims.strcat uu___4 ")" in
               Prims.strcat "(" uu___3 in
             Prims.strcat uu___1 uu___2 in
           let call1 =
             match hd.FStarC_Custard_Syntax.e with
             | FStarC_Custard_Syntax.EQual (n, uu___1) when
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Effect.op_Bang externs in
                     let uu___5 = FStarC_Custard_Syntax.string_of_name n in
                     FStarC_SMap.try_find uu___4 uu___5 in
                   match uu___3 with
                   | FStar_Pervasives_Native.Some v -> true
                   | uu___4 -> false in
                 if uu___2
                 then
                   (match e.FStarC_Custard_Syntax.ty with
                    | FStarC_Custard_Syntax.TBuf _0 -> true
                    | uu___3 -> false) ||
                     (match e.FStarC_Custard_Syntax.ty with
                      | FStarC_Custard_Syntax.TRef _0 -> true
                      | uu___3 -> false)
                 else false ->
                 let uu___2 =
                   let uu___3 = ty e.FStarC_Custard_Syntax.ty in
                   Prims.strcat uu___3 (Prims.strcat ")" call) in
                 Prims.strcat "(" uu___2
             | uu___1 -> call in
           match hd.FStarC_Custard_Syntax.e with
           | FStarC_Custard_Syntax.EQual (n, uu___1) when
               let uu___2 =
                 let uu___3 = FStarC_Effect.op_Bang void_fns in
                 let uu___4 = FStarC_Custard_Syntax.string_of_name n in
                 FStarC_SMap.try_find uu___3 uu___4 in
               match uu___2 with
               | FStar_Pervasives_Native.Some v -> true
               | uu___3 -> false ->
               ((let uu___3 =
                   let uu___4 = FStarC_Effect.op_Bang out in
                   Prims.strcat uu___4
                     (Prims.strcat ind (Prims.strcat call1 ";\n")) in
                 FStarC_Effect.op_Colon_Equals out uu___3);
                unit_value)
           | uu___1 -> call1))
     | FStarC_Custard_Syntax.ECast (e1, t) ->
         (match ((e1.FStarC_Custard_Syntax.ty), t) with
          | (FStarC_Custard_Syntax.TInt a, FStarC_Custard_Syntax.TInt b) when
              a = b -> c_expr out ind e1
          | (uu___, FStarC_Custard_Syntax.TFloat fw) when narrow_ty fw ->
              let uu___1 = narrow_pfx fw in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    c_rvalue out ind e1.FStarC_Custard_Syntax.ty e1 in
                  Prims.strcat uu___4 ")" in
                Prims.strcat
                  (match e1.FStarC_Custard_Syntax.ty with
                   | FStarC_Custard_Syntax.TInt (uu___4, uu___5) ->
                       "of_i64((int64_t)"
                   | FStarC_Custard_Syntax.TFloat
                       (FStarC_Custard_Syntax.Float64) -> "of_f64("
                   | uu___4 -> "of_f32(") uu___3 in
              Prims.strcat uu___1 uu___2
          | (FStarC_Custard_Syntax.TFloat fw, uu___) when narrow_ty fw ->
              let uu___1 =
                let uu___2 = ty t in
                let uu___3 =
                  let uu___4 =
                    let uu___5 = narrow_pfx fw in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 = c_expr out ind e1 in
                        Prims.strcat uu___8 ")" in
                      Prims.strcat "to_f32(" uu___7 in
                    Prims.strcat uu___5 uu___6 in
                  Prims.strcat ")" uu___4 in
                Prims.strcat uu___2 uu___3 in
              Prims.strcat "(" uu___1
          | uu___ ->
              let uu___1 =
                let uu___2 = ty t in
                let uu___3 =
                  let uu___4 =
                    c_rvalue out ind e1.FStarC_Custard_Syntax.ty e1 in
                  Prims.strcat ")" uu___4 in
                Prims.strcat uu___2 uu___3 in
              Prims.strcat "(" uu___1)
     | FStarC_Custard_Syntax.ECoerce (e1, t) ->
         if e1.FStarC_Custard_Syntax.ty = t
         then c_expr out ind e1
         else
           (let uu___ =
              let uu___1 = ty t in
              let uu___2 =
                let uu___3 = c_expr out ind e1 in Prims.strcat ")" uu___3 in
              Prims.strcat uu___1 uu___2 in
            Prims.strcat "(" uu___)
     | FStarC_Custard_Syntax.EProj (e1, uu___, f) ->
         let uu___1 = c_expr out ind e1 in
         proj uu___1 e1.FStarC_Custard_Syntax.ty f
     | FStarC_Custard_Syntax.EDiscrim (e1, cn) ->
         let uu___ = find_ctor cn in
         (match uu___ with
          | FStar_Pervasives_Native.Some (d, uu___1) ->
              if single_ctor d
              then "true"
              else
                (let uu___2 =
                   let uu___3 =
                     let uu___4 = c_expr out ind e1 in tag_of uu___4 d in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = c_tag cn in Prims.strcat uu___6 ")" in
                     Prims.strcat " == " uu___5 in
                   Prims.strcat uu___3 uu___4 in
                 Prims.strcat "(" uu___2)
          | FStar_Pervasives_Native.None ->
              let uu___1 =
                let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
                Prims.strcat "the constructor " uu___2 in
              reject uu___1
                ["It belongs to no type declaration in the program."])
     | FStarC_Custard_Syntax.ECtor (cn, args) ->
         ctor_lit out ind e.FStarC_Custard_Syntax.ty cn args
     | FStarC_Custard_Syntax.ERecord (uu___, fs) ->
         let uu___1 =
           let uu___2 = ty e.FStarC_Custard_Syntax.ty in
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_List.map
                     (fun uu___7 ->
                        match uu___7 with
                        | (f, v) ->
                            let uu___8 =
                              let uu___9 = c_var f in
                              let uu___10 =
                                let uu___11 =
                                  c_rvalue out ind v.FStarC_Custard_Syntax.ty
                                    v in
                                Prims.strcat " = " uu___11 in
                              Prims.strcat uu___9 uu___10 in
                            Prims.strcat "." uu___8) fs in
                 FStarC_String.concat ", " uu___6 in
               Prims.strcat uu___5 " }" in
             Prims.strcat "){ " uu___4 in
           Prims.strcat uu___2 uu___3 in
         Prims.strcat "(" uu___1
     | FStarC_Custard_Syntax.EOp
         ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
            FStarC_Custard_Syntax.po_ty = uu___;_},
          b::i::[])
         ->
         (match b.FStarC_Custard_Syntax.e with
          | FStarC_Custard_Syntax.EVar y when is_cell y -> lookup_var y
          | uu___1 ->
              let uu___2 = c_expr out ind b in
              let uu___3 =
                let uu___4 =
                  let uu___5 = c_rvalue out ind i.FStarC_Custard_Syntax.ty i in
                  Prims.strcat uu___5 "]" in
                Prims.strcat "[" uu___4 in
              Prims.strcat uu___2 uu___3)
     | FStarC_Custard_Syntax.EOp
         ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufSub;
            FStarC_Custard_Syntax.po_ty = uu___;_},
          b::i::[])
         ->
         let uu___1 =
           let uu___2 = c_expr out ind b in
           let uu___3 =
             let uu___4 =
               let uu___5 = c_rvalue out ind i.FStarC_Custard_Syntax.ty i in
               Prims.strcat uu___5 ")" in
             Prims.strcat " + " uu___4 in
           Prims.strcat uu___2 uu___3 in
         Prims.strcat "(" uu___1
     | FStarC_Custard_Syntax.EOp
         ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufNull;
            FStarC_Custard_Syntax.po_ty = uu___;_},
          [])
         ->
         let uu___1 =
           let uu___2 = ty e.FStarC_Custard_Syntax.ty in
           Prims.strcat uu___2 ")NULL" in
         Prims.strcat "(" uu___1
     | FStarC_Custard_Syntax.EOp
         ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufIsNull;
            FStarC_Custard_Syntax.po_ty = uu___;_},
          b::[])
         ->
         let uu___1 =
           let uu___2 = c_expr out ind b in Prims.strcat uu___2 " == NULL)" in
         Prims.strcat "(" uu___1
     | FStarC_Custard_Syntax.EOp
         ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufUnconst;
            FStarC_Custard_Syntax.po_ty = uu___;_},
          b::[])
         ->
         let uu___1 =
           let uu___2 = ty e.FStarC_Custard_Syntax.ty in
           let uu___3 =
             let uu___4 = c_expr out ind b in Prims.strcat ")" uu___4 in
           Prims.strcat uu___2 uu___3 in
         Prims.strcat "(" uu___1
     | FStarC_Custard_Syntax.EOp
         ({
            FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Commented
              (before, "");
            FStarC_Custard_Syntax.po_ty = uu___;_},
          {
            FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EConst
              (FStarC_Custard_Syntax.CUnit);
            FStarC_Custard_Syntax.ty = uu___1;
            FStarC_Custard_Syntax.eff = uu___2;_}::[])
         ->
         ((let uu___4 =
             let uu___5 = FStarC_Effect.op_Bang out in
             Prims.strcat uu___5
               (Prims.strcat ind
                  (Prims.strcat "/* " (Prims.strcat before " */\n"))) in
           FStarC_Effect.op_Colon_Equals out uu___4);
          unit_value)
     | FStarC_Custard_Syntax.EOp
         ({
            FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Commented
              (before, after);
            FStarC_Custard_Syntax.po_ty = uu___;_},
          b::[])
         ->
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 = c_rvalue out ind e.FStarC_Custard_Syntax.ty b in
               Prims.strcat uu___4
                 (Prims.strcat " /* " (Prims.strcat after " */")) in
             Prims.strcat " */ " uu___3 in
           Prims.strcat before uu___2 in
         Prims.strcat "/* " uu___1
     | FStarC_Custard_Syntax.EOp
         ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
            FStarC_Custard_Syntax.po_ty = uu___;_},
          uu___1)
         ->
         let uu___2 =
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 = FStarC_Effect.op_Bang current in
                 Prims.strcat uu___6
                   " uses a static array where C needs an expression." in
               Prims.strcat "Custard: " uu___5 in
             FStarC_Errors_Msg.text uu___4 in
           [uu___3;
           FStarC_Errors_Msg.text
             "A Pulse.Lib.GlobalArray.static_array is a braced initializer, and C accepts one of those only in a declaration -- so it can be the body of a top-level definition and nothing else.";
           FStarC_Errors_Msg.text
             "Bind it to a top-level definition and use that name here."] in
         FStarC_Errors.raise_error0
           FStarC_Errors_Codes.Error_CustardBadStaticArray ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
           (Obj.magic uu___2)
     | FStarC_Custard_Syntax.EOp (o, a::b::[]) when
         if
           (match o.FStarC_Custard_Syntax.po_op with
            | FStarC_Custard_Syntax.Eq -> true
            | uu___ -> false) ||
             (match o.FStarC_Custard_Syntax.po_op with
              | FStarC_Custard_Syntax.Neq -> true
              | uu___ -> false)
         then is_string_ty a.FStarC_Custard_Syntax.ty
         else false ->
         let uu___ =
           let uu___1 = c_expr out ind a in
           let uu___2 =
             let uu___3 =
               let uu___4 = c_expr out ind b in
               Prims.strcat uu___4
                 (Prims.strcat ") "
                    (Prims.strcat
                       (if
                          match o.FStarC_Custard_Syntax.po_op with
                          | FStarC_Custard_Syntax.Eq -> true
                          | uu___5 -> false
                        then "=="
                        else "!=") " 0)")) in
             Prims.strcat ", " uu___3 in
           Prims.strcat uu___1 uu___2 in
         Prims.strcat "(strcmp(" uu___
     | FStarC_Custard_Syntax.EOp (o, a::b::[]) when
         if
           (match o.FStarC_Custard_Syntax.po_op with
            | FStarC_Custard_Syntax.Eq -> true
            | uu___ -> false) ||
             (match o.FStarC_Custard_Syntax.po_op with
              | FStarC_Custard_Syntax.Neq -> true
              | uu___ -> false)
         then
           let uu___ = eq_fn_of a.FStarC_Custard_Syntax.ty in
           match uu___ with
           | FStar_Pervasives_Native.Some v -> true
           | uu___1 -> false
         else false ->
         let g =
           let uu___ = eq_fn_of a.FStarC_Custard_Syntax.ty in
           match uu___ with
           | FStar_Pervasives_Native.Some g1 -> g1
           | FStar_Pervasives_Native.None -> "" in
         let uu___ =
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 = c_expr out ind a in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = c_expr out ind b in
                     Prims.strcat uu___7 "))" in
                   Prims.strcat ", " uu___6 in
                 Prims.strcat uu___4 uu___5 in
               Prims.strcat "(" uu___3 in
             Prims.strcat g uu___2 in
           Prims.strcat
             (if
                match o.FStarC_Custard_Syntax.po_op with
                | FStarC_Custard_Syntax.Neq -> true
                | uu___2 -> false
              then "!"
              else "") uu___1 in
         Prims.strcat "(" uu___
     | FStarC_Custard_Syntax.EOp (o, a::b::[]) when
         let uu___ = narrow_call o in
         match uu___ with
         | FStar_Pervasives_Native.Some v -> true
         | uu___1 -> false ->
         let uu___ =
           let uu___1 = narrow_call o in
           match uu___1 with | FStar_Pervasives_Native.Some v -> v in
         let uu___1 =
           let uu___2 =
             let uu___3 = c_rvalue out ind a.FStarC_Custard_Syntax.ty a in
             let uu___4 =
               let uu___5 =
                 let uu___6 = c_rvalue out ind b.FStarC_Custard_Syntax.ty b in
                 Prims.strcat uu___6 ")" in
               Prims.strcat ", " uu___5 in
             Prims.strcat uu___3 uu___4 in
           Prims.strcat "(" uu___2 in
         Prims.strcat uu___ uu___1
     | FStarC_Custard_Syntax.EOp (o, a::b::[]) when
         ((match o.FStarC_Custard_Syntax.po_op with
           | FStarC_Custard_Syntax.And -> true
           | uu___ -> false) ||
            (match o.FStarC_Custard_Syntax.po_op with
             | FStarC_Custard_Syntax.Or -> true
             | uu___ -> false))
           && (Prims.not (FStarC_Custard_Syntax.at_int_width o))
         ->
         let av = c_expr out ind a in
         let bout = FStarC_Effect.mk_ref "" in
         let bv = c_expr bout (Prims.strcat ind "  ") b in
         let uu___ = let uu___1 = FStarC_Effect.op_Bang bout in uu___1 = "" in
         if uu___
         then
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = infix_op o in
                   match uu___5 with | FStar_Pervasives_Native.Some v -> v in
                 Prims.strcat uu___4 (Prims.strcat " " (Prims.strcat bv ")")) in
               Prims.strcat " " uu___3 in
             Prims.strcat av uu___2 in
           Prims.strcat "(" uu___1
         else
           (let x = fresh "sc" in
            (let uu___2 =
               let uu___3 = FStarC_Effect.op_Bang out in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = decl_of e.FStarC_Custard_Syntax.ty x in
                   let uu___7 =
                     let uu___8 =
                       let uu___9 =
                         let uu___10 =
                           let uu___11 =
                             let uu___12 =
                               let uu___13 =
                                 let uu___14 =
                                   let uu___15 =
                                     let uu___16 = FStarC_Effect.op_Bang bout in
                                     Prims.strcat uu___16
                                       (Prims.strcat ind
                                          (Prims.strcat "  "
                                             (Prims.strcat x
                                                (Prims.strcat " = "
                                                   (Prims.strcat bv
                                                      (Prims.strcat ";\n"
                                                         (Prims.strcat ind
                                                            "}\n"))))))) in
                                   Prims.strcat ") {\n" uu___15 in
                                 Prims.strcat x uu___14 in
                               Prims.strcat
                                 (if
                                    match o.FStarC_Custard_Syntax.po_op with
                                    | FStarC_Custard_Syntax.Or -> true
                                    | uu___14 -> false
                                  then "!"
                                  else "") uu___13 in
                             Prims.strcat "if (" uu___12 in
                           Prims.strcat ind uu___11 in
                         Prims.strcat ";\n" uu___10 in
                       Prims.strcat av uu___9 in
                     Prims.strcat " = " uu___8 in
                   Prims.strcat uu___6 uu___7 in
                 Prims.strcat ind uu___5 in
               Prims.strcat uu___3 uu___4 in
             FStarC_Effect.op_Colon_Equals out uu___2);
            x)
     | FStarC_Custard_Syntax.EOp (o, a::b::[]) when
         let uu___ = infix_op o in
         match uu___ with
         | FStar_Pervasives_Native.Some v -> true
         | uu___1 -> false ->
         let shift =
           (match o.FStarC_Custard_Syntax.po_op with
            | FStarC_Custard_Syntax.BShiftL -> true
            | uu___ -> false) ||
             (match o.FStarC_Custard_Syntax.po_op with
              | FStarC_Custard_Syntax.BShiftR -> true
              | uu___ -> false) in
         let av =
           if
             shift ||
               (match b.FStarC_Custard_Syntax.e with
                | FStarC_Custard_Syntax.EConst _0 -> true
                | uu___ -> false)
           then c_expr out ind a
           else c_rvalue out ind a.FStarC_Custard_Syntax.ty a in
         let bv =
           if
             (Prims.not shift) &&
               (match a.FStarC_Custard_Syntax.e with
                | FStarC_Custard_Syntax.EConst _0 -> true
                | uu___ -> false)
           then c_expr out ind b
           else c_rvalue out ind b.FStarC_Custard_Syntax.ty b in
         let wrap s =
           let uu___ = widen_operands o in
           match uu___ with
           | FStar_Pervasives_Native.Some c ->
               let uu___1 = group s in Prims.strcat c uu___1
           | FStar_Pervasives_Native.None -> s in
         let uu___ =
           let uu___1 =
             let uu___2 = wrap av in
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 = infix_op o in
                   match uu___6 with | FStar_Pervasives_Native.Some v -> v in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = wrap bv in Prims.strcat uu___8 ")" in
                   Prims.strcat " " uu___7 in
                 Prims.strcat uu___5 uu___6 in
               Prims.strcat " " uu___4 in
             Prims.strcat uu___2 uu___3 in
           Prims.strcat "(" uu___1 in
         truncate o uu___
     | FStarC_Custard_Syntax.EOp (o, a::[]) when
         let uu___ = prefix_op o in
         match uu___ with
         | FStar_Pervasives_Native.Some v -> true
         | uu___1 -> false ->
         let uu___ =
           let uu___1 =
             let uu___2 =
               let uu___3 = prefix_op o in
               match uu___3 with | FStar_Pervasives_Native.Some v -> v in
             let uu___3 =
               let uu___4 = let uu___5 = c_expr out ind a in group uu___5 in
               Prims.strcat uu___4 ")" in
             Prims.strcat uu___2 uu___3 in
           Prims.strcat "(" uu___1 in
         truncate o uu___
     | FStarC_Custard_Syntax.EOp (o, args) ->
         let uu___ =
           let uu___1 =
             let uu___2 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                 (FStarC_List.length args) in
             Prims.strcat uu___2 " arguments" in
           Prims.strcat "an operator applied to " uu___1 in
         reject uu___ []
     | FStarC_Custard_Syntax.EFun uu___ ->
         reject "a lambda that captures a local variable"
           ["C has no closures, and this one is not closed, so it cannot be lifted to a top-level function (section 19.12).";
           "Mark the parameter it is passed to [@@@monomorphize] so that it is specialized away (section 3.1), or name the captured values as extra parameters of a top-level function."]
     | FStarC_Custard_Syntax.ETuple uu___ ->
         reject "an anonymous tuple"
           ["Tuples reach the backend as FStar.Pervasives.Native.MktupleN."]
     | FStarC_Custard_Syntax.ERaise uu___ ->
         reject "an exception" ["C has no exceptions."]
     | FStarC_Custard_Syntax.ETry uu___ ->
         reject "an exception" ["C has no exceptions."]
     | uu___ -> reject "this term" [])
and hoist (out : Prims.string FStarC_Effect.ref) (ind : Prims.string)
  (e : FStarC_Custard_Syntax.expr) : Prims.string=
  if
    match e.FStarC_Custard_Syntax.ty with
    | FStarC_Custard_Syntax.TUnit -> true
    | uu___ -> false
  then
    ((let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang out in
        let uu___3 = emit ind D_Ignore e in Prims.strcat uu___2 uu___3 in
      FStarC_Effect.op_Colon_Equals out uu___1);
     unit_value)
  else
    (let x = fresh "t" in
     let body = emit ind (D_Assign x) e in
     match FStarC_String.split [10] body with
     | l::""::[] when
         let uu___ = is_pure e in
         if uu___
         then starts_with l (Prims.strcat ind (Prims.strcat x " = "))
         else false ->
         FStarC_String.substring l
           (((FStarC_String.length ind) + (FStarC_String.length x)) +
              (Prims.of_int 3))
           ((((FStarC_String.length l) - (FStarC_String.length ind)) -
               (FStarC_String.length x))
              - (Prims.of_int 4))
     | uu___ ->
         ((let uu___2 =
             let uu___3 = FStarC_Effect.op_Bang out in
             let uu___4 =
               let uu___5 =
                 let uu___6 = decl_of e.FStarC_Custard_Syntax.ty x in
                 Prims.strcat uu___6 (Prims.strcat ";\n" body) in
               Prims.strcat ind uu___5 in
             Prims.strcat uu___3 uu___4 in
           FStarC_Effect.op_Colon_Equals out uu___2);
          x))
and proj (v : Prims.string) (t : FStarC_Custard_Syntax.cty)
  (f : Prims.string) : Prims.string=
  match t with
  | FStarC_Custard_Syntax.TApp (n, uu___) ->
      let uu___1 = find_type n in
      (match uu___1 with
       | FStar_Pervasives_Native.Some d when single_ctor d ->
           let uu___2 = let uu___3 = c_var f in Prims.strcat "." uu___3 in
           Prims.strcat v uu___2
       | FStar_Pervasives_Native.Some
           { FStarC_Custard_Syntax.dt_name = uu___2;
             FStarC_Custard_Syntax.dt_params = uu___3;
             FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TRecord
               uu___4;
             FStarC_Custard_Syntax.dt_flags = uu___5;_}
           ->
           let uu___6 = let uu___7 = c_var f in Prims.strcat "." uu___7 in
           Prims.strcat v uu___6
       | FStar_Pervasives_Native.Some d ->
           (match d.FStarC_Custard_Syntax.dt_body with
            | FStarC_Custard_Syntax.TVariant cs ->
                let uu___2 =
                  FStarC_List.tryFind
                    (fun uu___3 ->
                       match uu___3 with
                       | (uu___4, fs) ->
                           FStarC_List.existsb
                             (fun uu___5 ->
                                match uu___5 with | (g, uu___6) -> g = f) fs)
                    cs in
                (match uu___2 with
                 | FStar_Pervasives_Native.Some (cn, cfs) ->
                     let uu___3 = arm_sel cn cfs f in Prims.strcat v uu___3
                 | FStar_Pervasives_Native.None ->
                     reject (Prims.strcat "the field " f)
                       ["No constructor declares it."])
            | uu___2 -> reject (Prims.strcat "the field " f) [])
       | FStar_Pervasives_Native.None ->
           let uu___2 =
             let uu___3 = FStarC_Custard_Syntax.string_of_name n in
             Prims.strcat "a projection out of " uu___3 in
           reject uu___2 ["The type has no declaration in the program."])
  | uu___ ->
      reject (Prims.strcat "the field " f)
        ["Its owner is not a declared type."]
and tag_of (v : Prims.string) (d : FStarC_Custard_Syntax.dtype) :
  Prims.string=
  let uu___ = is_enum d in if uu___ then v else Prims.strcat v ".tag"
and c_rvalue (out : Prims.string FStarC_Effect.ref) (ind : Prims.string)
  (target : FStarC_Custard_Syntax.cty) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst c ->
      let uu___ = converted_int target e.FStarC_Custard_Syntax.ty c in
      (match uu___ with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None -> c_expr out ind e)
  | uu___ -> c_expr out ind e
and ctor_lit (out : Prims.string FStarC_Effect.ref) (ind : Prims.string)
  (t : FStarC_Custard_Syntax.cty) (cn : FStarC_Custard_Syntax.name)
  (args : FStarC_Custard_Syntax.expr Prims.list) : Prims.string=
  let uu___ = find_ctor cn in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
        Prims.strcat "the constructor " uu___2 in
      reject uu___1 ["It belongs to no type declaration in the program."]
  | FStar_Pervasives_Native.Some (d, fields) ->
      let vals =
        FStarC_List.map
          (fun a -> c_rvalue out ind a.FStarC_Custard_Syntax.ty a) args in
      let named = zip_fields fields vals in
      let uu___1 = is_enum d in
      if uu___1
      then c_tag cn
      else
        if single_ctor d
        then
          (let uu___2 =
             let uu___3 = c_name d.FStarC_Custard_Syntax.dt_name in
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     FStarC_List.map
                       (fun uu___8 ->
                          match uu___8 with
                          | (f, v) ->
                              let uu___9 =
                                let uu___10 = c_var f in
                                Prims.strcat uu___10 (Prims.strcat " = " v) in
                              Prims.strcat "." uu___9) named in
                   FStarC_String.concat ", " uu___7 in
                 Prims.strcat uu___6 " }" in
               Prims.strcat "){ " uu___5 in
             Prims.strcat uu___3 uu___4 in
           Prims.strcat "(" uu___2)
        else
          if (match fields with | [] -> true | uu___2 -> false)
          then
            (let uu___2 =
               let uu___3 = c_name d.FStarC_Custard_Syntax.dt_name in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = c_tag cn in Prims.strcat uu___6 " }" in
                 Prims.strcat "){ .tag = " uu___5 in
               Prims.strcat uu___3 uu___4 in
             Prims.strcat "(" uu___2)
          else
            (let uu___2 =
               let uu___3 = c_name d.FStarC_Custard_Syntax.dt_name in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = c_tag cn in
                   let uu___7 =
                     let uu___8 =
                       let uu___9 = arm_name cn in
                       let uu___10 =
                         let uu___11 =
                           let uu___12 =
                             if arm_flat fields
                             then
                               FStar_Pervasives_Native.snd
                                 (FStarC_List.hd named)
                             else
                               (let uu___13 =
                                  let uu___14 =
                                    let uu___15 =
                                      FStarC_List.map
                                        (fun uu___16 ->
                                           match uu___16 with
                                           | (f, v) ->
                                               let uu___17 =
                                                 let uu___18 = c_var f in
                                                 Prims.strcat uu___18
                                                   (Prims.strcat " = " v) in
                                               Prims.strcat "." uu___17)
                                        named in
                                    FStarC_String.concat ", " uu___15 in
                                  Prims.strcat uu___14 " }" in
                                Prims.strcat "{ " uu___13) in
                           Prims.strcat uu___12 " } }" in
                         Prims.strcat " = " uu___11 in
                       Prims.strcat uu___9 uu___10 in
                     Prims.strcat ", .val = { ." uu___8 in
                   Prims.strcat uu___6 uu___7 in
                 Prims.strcat "){ .tag = " uu___5 in
               Prims.strcat uu___3 uu___4 in
             Prims.strcat "(" uu___2)
and finish (ind : Prims.string) (d : dest) (s : Prims.string) : Prims.string=
  match d with
  | D_Return when FStarC_Effect.op_Bang void_ret ->
      if s = unit_value
      then ""
      else Prims.strcat ind (Prims.strcat "(void)(" (Prims.strcat s ");\n"))
  | D_Return ->
      Prims.strcat ind (Prims.strcat "return " (Prims.strcat s ";\n"))
  | D_Assign x ->
      Prims.strcat ind
        (Prims.strcat x (Prims.strcat " = " (Prims.strcat s ";\n")))
  | D_Ignore ->
      if s = unit_value
      then ""
      else Prims.strcat ind (Prims.strcat "(void)(" (Prims.strcat s ");\n"))
and emit (ind : Prims.string) (d : dest) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  let ind' = Prims.strcat ind "  " in
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet (x, FStarC_Custard_Syntax.TUnit, e1, e2) ->
      let saved = FStarC_Effect.op_Bang scope in
      let s1 = emit ind D_Ignore e1 in
      (bind_alias x unit_value;
       (let s2 = emit ind d e2 in
        FStarC_Effect.op_Colon_Equals scope saved; Prims.strcat s1 s2))
  | FStarC_Custard_Syntax.ELet
      (x, uu___,
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EOp
           ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
              FStarC_Custard_Syntax.po_ty = uu___1;_},
            { FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EVar y;
              FStarC_Custard_Syntax.ty = uu___2;
              FStarC_Custard_Syntax.eff = uu___3;_}::uu___4::[]);
         FStarC_Custard_Syntax.ty = uu___5;
         FStarC_Custard_Syntax.eff = uu___6;_},
       e2)
      when
      let uu___7 = is_cell y in
      if uu___7 then let uu___8 = mutates y e2 in Prims.not uu___8 else false
      ->
      let saved = FStarC_Effect.op_Bang scope in
      ((let uu___8 = lookup_var y in bind_alias x uu___8);
       (let s2 = emit ind d e2 in
        FStarC_Effect.op_Colon_Equals scope saved; s2))
  | FStarC_Custard_Syntax.ELet (x, uu___, e1, e2) when is_stable e1 ->
      let out = FStarC_Effect.mk_ref "" in
      let path = c_expr out ind e1 in
      let saved = FStarC_Effect.op_Bang scope in
      (bind_alias x path;
       (let s2 = emit ind d e2 in
        FStarC_Effect.op_Colon_Equals scope saved;
        (let uu___3 = FStarC_Effect.op_Bang out in Prims.strcat uu___3 s2)))
  | FStarC_Custard_Syntax.ELet
      (x, FStarC_Custard_Syntax.TRef t,
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EOp
           ({
              FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate
                (FStarC_Custard_Syntax.LStack);
              FStarC_Custard_Syntax.po_ty = uu___;_},
            init::len::[]);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       e2)
      when
      let uu___3 =
        if is_one len then FStarC_Custard_Syntax.is_droppable init else false in
      if uu___3 then cell_dead x e2 else false ->
      let uu___3 = drop_writes x e2 in emit ind d uu___3
  | FStarC_Custard_Syntax.ELet
      (x, FStarC_Custard_Syntax.TBuf t,
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EOp
           ({
              FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate
                (FStarC_Custard_Syntax.LStack);
              FStarC_Custard_Syntax.po_ty = uu___;_},
            init::len::[]);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       e2)
      when
      let uu___3 =
        if is_one len then FStarC_Custard_Syntax.is_droppable init else false in
      if uu___3 then cell_dead x e2 else false ->
      let uu___3 = drop_writes x e2 in emit ind d uu___3
  | FStarC_Custard_Syntax.ELet
      (x, FStarC_Custard_Syntax.TRef t,
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EOp
           ({
              FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate
                (FStarC_Custard_Syntax.LStack);
              FStarC_Custard_Syntax.po_ty = uu___;_},
            init::len::[]);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       e2)
      when is_one len ->
      let out = FStarC_Effect.mk_ref "" in
      let iv = c_rvalue out ind t init in
      let saved = FStarC_Effect.op_Bang scope in
      let nm = bind_cell x in
      let s2 = emit ind d e2 in
      (FStarC_Effect.op_Colon_Equals scope saved;
       (let uu___4 = FStarC_Effect.op_Bang out in
        let uu___5 =
          let uu___6 =
            let uu___7 = decl_of t nm in
            Prims.strcat uu___7
              (Prims.strcat " = " (Prims.strcat iv (Prims.strcat ";\n" s2))) in
          Prims.strcat ind uu___6 in
        Prims.strcat uu___4 uu___5))
  | FStarC_Custard_Syntax.ELet
      (x, FStarC_Custard_Syntax.TBuf t,
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EOp
           ({
              FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate
                (FStarC_Custard_Syntax.LStack);
              FStarC_Custard_Syntax.po_ty = uu___;_},
            init::len::[]);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       e2)
      when is_one len ->
      let out = FStarC_Effect.mk_ref "" in
      let iv = c_rvalue out ind t init in
      let saved = FStarC_Effect.op_Bang scope in
      let nm = bind_cell x in
      let s2 = emit ind d e2 in
      (FStarC_Effect.op_Colon_Equals scope saved;
       (let uu___4 = FStarC_Effect.op_Bang out in
        let uu___5 =
          let uu___6 =
            let uu___7 = decl_of t nm in
            Prims.strcat uu___7
              (Prims.strcat " = " (Prims.strcat iv (Prims.strcat ";\n" s2))) in
          Prims.strcat ind uu___6 in
        Prims.strcat uu___4 uu___5))
  | FStarC_Custard_Syntax.ELet
      (x, FStarC_Custard_Syntax.TBuf t,
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EOp
           ({
              FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate
                lt;
              FStarC_Custard_Syntax.po_ty = uu___;_},
            init::len::[]);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_},
       e2)
      when
      Prims.not
        ((match lt with
          | FStarC_Custard_Syntax.LStack -> true
          | uu___3 -> false) && (is_one len))
      ->
      let saved = FStarC_Effect.op_Bang scope in
      let nm = bind_var x in
      let s1 =
        let saved' = FStarC_Effect.op_Bang scope in
        FStarC_Effect.op_Colon_Equals scope saved;
        (let s =
           emit_alloc ind D_Ignore (FStar_Pervasives_Native.Some nm) lt
             (FStarC_Custard_Syntax.TBuf t) init len in
         FStarC_Effect.op_Colon_Equals scope saved'; s) in
      let s2 = emit ind d e2 in
      (FStarC_Effect.op_Colon_Equals scope saved; Prims.strcat s1 s2)
  | FStarC_Custard_Syntax.ELet (x, uu___, e1, e2) when
      let uu___1 = FStarC_Custard_Syntax.is_droppable e1 in
      if uu___1
      then
        let uu___2 = let uu___3 = vars_of e2 in FStarC_List.mem x uu___3 in
        Prims.not uu___2
      else false -> emit ind d e2
  | FStarC_Custard_Syntax.ELet (x, t, e1, e2) ->
      let saved = FStarC_Effect.op_Bang scope in
      let s1 =
        if is_stmt e1
        then
          let x1 = bind_var x in
          let body =
            let saved' = FStarC_Effect.op_Bang scope in
            FStarC_Effect.op_Colon_Equals scope saved;
            (let s = emit ind (D_Assign x1) e1 in
             FStarC_Effect.op_Colon_Equals scope saved'; s) in
          match FStarC_String.split [10] body with
          | l::""::[] when
              starts_with l (Prims.strcat ind (Prims.strcat x1 " = ")) ->
              let uu___ =
                let uu___1 = decl_of t x1 in
                let uu___2 =
                  let uu___3 =
                    FStarC_String.substring l
                      ((FStarC_String.length ind) + (FStarC_String.length x1))
                      (((FStarC_String.length l) - (FStarC_String.length ind))
                         - (FStarC_String.length x1)) in
                  Prims.strcat uu___3 "\n" in
                Prims.strcat uu___1 uu___2 in
              Prims.strcat ind uu___
          | uu___ ->
              let uu___1 =
                let uu___2 = decl_of t x1 in
                Prims.strcat uu___2 (Prims.strcat ";\n" body) in
              Prims.strcat ind uu___1
        else
          (let out = FStarC_Effect.mk_ref "" in
           let v = c_rvalue out ind t e1 in
           let x1 = bind_var x in
           let x2 =
             let uu___ =
               let uu___1 = binds_by_ref t in
               if uu___1 then is_lvalue e1 else false in
             if uu___ then Prims.strcat "&" x1 else x1 in
           let uu___ = FStarC_Effect.op_Bang out in
           let uu___1 =
             let uu___2 =
               let uu___3 = decl_of t x2 in
               Prims.strcat uu___3
                 (Prims.strcat " = " (Prims.strcat v ";\n")) in
             Prims.strcat ind uu___2 in
           Prims.strcat uu___ uu___1) in
      let s2 = emit ind d e2 in
      (FStarC_Effect.op_Colon_Equals scope saved; Prims.strcat s1 s2)
  | FStarC_Custard_Syntax.ESeq (e1, e2) ->
      let uu___ = emit ind D_Ignore e1 in
      let uu___1 = emit ind d e2 in Prims.strcat uu___ uu___1
  | FStarC_Custard_Syntax.EIf (c, t, f) ->
      let out = FStarC_Effect.mk_ref "" in
      let cs = c_expr out ind c in
      let tt = emit ind' d t in
      let ft = emit ind' d f in
      let uu___ = FStarC_Effect.op_Bang out in
      let uu___1 =
        if (tt = "") && (ft = "")
        then ""
        else
          if tt = ""
          then
            (let uu___2 =
               let uu___3 =
                 let uu___4 = negate cs in
                 let uu___5 =
                   let uu___6 = brace ind ft in Prims.strcat ")" uu___6 in
                 Prims.strcat uu___4 uu___5 in
               Prims.strcat "if (" uu___3 in
             Prims.strcat ind uu___2)
          else
            (let uu___2 =
               let uu___3 =
                 let uu___4 = unparen cs in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = brace ind tt in
                     let uu___8 =
                       if ft = ""
                       then ""
                       else
                         (let uu___9 =
                            let uu___10 = brace ind ft in
                            Prims.strcat "else" uu___10 in
                          Prims.strcat ind uu___9) in
                     Prims.strcat uu___7 uu___8 in
                   Prims.strcat ")" uu___6 in
                 Prims.strcat uu___4 uu___5 in
               Prims.strcat "if (" uu___3 in
             Prims.strcat ind uu___2) in
      Prims.strcat uu___ uu___1
  | FStarC_Custard_Syntax.EMatch (scrut, brs) -> emit_match ind d scrut brs
  | FStarC_Custard_Syntax.EWhile (c, body) ->
      let out = FStarC_Effect.mk_ref "" in
      let cs = c_expr out ind' c in
      let uu___ =
        let uu___1 = let uu___2 = FStarC_Effect.op_Bang out in uu___2 = "" in
        if uu___1
        then
          let uu___2 =
            let uu___3 =
              let uu___4 = unparen cs in Prims.strcat uu___4 ") {\n" in
            Prims.strcat "while (" uu___3 in
          Prims.strcat ind uu___2
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_Effect.op_Bang out in
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = negate cs in
                     Prims.strcat uu___8 ") { break; }\n" in
                   Prims.strcat "if (" uu___7 in
                 Prims.strcat ind' uu___6 in
               Prims.strcat uu___4 uu___5 in
             Prims.strcat "while (true) {\n" uu___3 in
           Prims.strcat ind uu___2) in
      let uu___1 =
        let uu___2 = emit ind' D_Ignore body in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              match d with
              | D_Ignore -> ""
              | uu___6 -> finish ind d unit_value in
            Prims.strcat "}\n" uu___5 in
          Prims.strcat ind uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat uu___ uu___1
  | FStarC_Custard_Syntax.EAbort s ->
      let uu___ =
        let uu___1 =
          let uu___2 = escape s in
          Prims.strcat uu___2
            (Prims.strcat " */\n" (Prims.strcat ind "abort();\n")) in
        Prims.strcat "/* " uu___1 in
      Prims.strcat ind uu___
  | FStarC_Custard_Syntax.EOp
      ({
         FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Commented
           (before, "");
         FStarC_Custard_Syntax.po_ty = uu___;_},
       {
         FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EConst
           (FStarC_Custard_Syntax.CUnit);
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_}::[])
      ->
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 = unit_result ind d in Prims.strcat " */\n" uu___6 in
          Prims.strcat before uu___5 in
        Prims.strcat "/* " uu___4 in
      Prims.strcat ind uu___3
  | FStarC_Custard_Syntax.EOp
      ({
         FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Commented
           (before, after);
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      when
      if match d with | D_Ignore -> true | uu___1 -> false
      then FStarC_Custard_Syntax.is_droppable b
      else false ->
      Prims.strcat ind
        (Prims.strcat "/* "
           (Prims.strcat before
              (Prims.strcat " */\n"
                 (Prims.strcat ind
                    (Prims.strcat "/* " (Prims.strcat after " */\n"))))))
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate lt;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       init::len::[])
      ->
      emit_alloc ind d FStar_Pervasives_Native.None lt
        e.FStarC_Custard_Syntax.ty init len
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::i::v::[])
      ->
      let out = FStarC_Effect.mk_ref "" in
      let lhs =
        match b.FStarC_Custard_Syntax.e with
        | FStarC_Custard_Syntax.EVar y when is_cell y -> lookup_var y
        | uu___1 ->
            let uu___2 = c_expr out ind b in
            let uu___3 =
              let uu___4 =
                let uu___5 = c_rvalue out ind i.FStarC_Custard_Syntax.ty i in
                Prims.strcat uu___5 "]" in
              Prims.strcat "[" uu___4 in
            Prims.strcat uu___2 uu___3 in
      let v1 = c_rvalue out ind v.FStarC_Custard_Syntax.ty v in
      let uu___1 = FStarC_Effect.op_Bang out in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = unit_result ind d in Prims.strcat ";\n" uu___7 in
              Prims.strcat v1 uu___6 in
            Prims.strcat " = " uu___5 in
          Prims.strcat lhs uu___4 in
        Prims.strcat ind uu___3 in
      Prims.strcat uu___1 uu___2
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufFree;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       { FStarC_Custard_Syntax.e = FStarC_Custard_Syntax.EVar y;
         FStarC_Custard_Syntax.ty = uu___1;
         FStarC_Custard_Syntax.eff = uu___2;_}::[])
      when is_cell y -> unit_result ind d
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufFree;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      ->
      let out = FStarC_Effect.mk_ref "" in
      let b1 = c_expr out ind b in
      let uu___1 = FStarC_Effect.op_Bang out in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = unit_result ind d in Prims.strcat ");\n" uu___6 in
            Prims.strcat b1 uu___5 in
          Prims.strcat "free(" uu___4 in
        Prims.strcat ind uu___3 in
      Prims.strcat uu___1 uu___2
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufBlit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       src::si::dst::di::len::[])
      ->
      let out = FStarC_Effect.mk_ref "" in
      let elt =
        match dst.FStarC_Custard_Syntax.ty with
        | FStarC_Custard_Syntax.TBuf e1 -> ty e1
        | FStarC_Custard_Syntax.TRef e1 -> ty e1
        | uu___1 -> reject "a blit whose destination is not a pointer" [] in
      let srcv = c_expr out ind src in
      let siv = c_rvalue out ind si.FStarC_Custard_Syntax.ty si in
      let dstv = c_expr out ind dst in
      let div = c_rvalue out ind di.FStarC_Custard_Syntax.ty di in
      let lenv = c_rvalue out ind len.FStarC_Custard_Syntax.ty len in
      let uu___1 = FStarC_Effect.op_Bang out in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          let uu___12 =
                            let uu___13 = group lenv in
                            let uu___14 =
                              let uu___15 =
                                let uu___16 =
                                  let uu___17 = unit_result ind d in
                                  Prims.strcat "));\n" uu___17 in
                                Prims.strcat elt uu___16 in
                              Prims.strcat " * sizeof(" uu___15 in
                            Prims.strcat uu___13 uu___14 in
                          Prims.strcat ", " uu___12 in
                        Prims.strcat siv uu___11 in
                      Prims.strcat " + " uu___10 in
                    Prims.strcat srcv uu___9 in
                  Prims.strcat ", " uu___8 in
                Prims.strcat div uu___7 in
              Prims.strcat " + " uu___6 in
            Prims.strcat dstv uu___5 in
          Prims.strcat "memmove(" uu___4 in
        Prims.strcat ind uu___3 in
      Prims.strcat uu___1 uu___2
  | uu___ ->
      let out = FStarC_Effect.mk_ref "" in
      let s = c_rvalue out ind e.FStarC_Custard_Syntax.ty e in
      let uu___1 = FStarC_Effect.op_Bang out in
      let uu___2 = finish ind d s in Prims.strcat uu___1 uu___2
and unit_result (ind : Prims.string) (d : dest) : Prims.string=
  match d with | D_Ignore -> "" | uu___ -> finish ind d unit_value
and emit_alloc (ind : Prims.string) (d : dest)
  (nm : Prims.string FStar_Pervasives_Native.option)
  (lt : FStarC_Custard_Syntax.lifetime) (t : FStarC_Custard_Syntax.cty)
  (init : FStarC_Custard_Syntax.expr) (len : FStarC_Custard_Syntax.expr) :
  Prims.string=
  let out = FStarC_Effect.mk_ref "" in
  let iv = c_rvalue out ind init.FStarC_Custard_Syntax.ty init in
  let lv = c_rvalue out ind len.FStarC_Custard_Syntax.ty len in
  let elt =
    match t with
    | FStarC_Custard_Syntax.TBuf e -> ty e
    | FStarC_Custard_Syntax.TRef e -> ty e
    | uu___ -> reject "an allocation whose result is not a pointer" [] in
  let arr =
    match nm with
    | FStar_Pervasives_Native.Some x -> x
    | FStar_Pervasives_Native.None -> fresh "buf" in
  let done_ s =
    match nm with
    | FStar_Pervasives_Native.Some uu___ -> ""
    | FStar_Pervasives_Native.None -> finish ind d s in
  let i = fresh "i" in
  let elt_of =
    match t with
    | FStarC_Custard_Syntax.TBuf e -> e
    | FStarC_Custard_Syntax.TRef e -> e
    | uu___ -> t in
  if
    (match lt with | FStarC_Custard_Syntax.LStack -> true | uu___ -> false)
      && (is_one len)
  then
    let uu___ = FStarC_Effect.op_Bang out in
    let uu___1 =
      let uu___2 =
        let uu___3 = decl_of elt_of arr in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 = done_ (Prims.strcat "&" arr) in
              Prims.strcat ";\n" uu___7 in
            Prims.strcat iv uu___6 in
          Prims.strcat " = " uu___5 in
        Prims.strcat uu___3 uu___4 in
      Prims.strcat ind uu___2 in
    Prims.strcat uu___ uu___1
  else
    (let scalar_elt =
       match elt_of with
       | FStarC_Custard_Syntax.TInt uu___ -> true
       | FStarC_Custard_Syntax.TFloat uu___ -> true
       | FStarC_Custard_Syntax.TBuf uu___ -> true
       | FStarC_Custard_Syntax.TRef uu___ -> true
       | FStarC_Custard_Syntax.TApp (n, []) ->
           let uu___ = builtin_type n in
           (FStar_Pervasives_Native.Some "bool") = uu___
       | uu___ -> false in
     let const_len =
       match len.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt
           (n, uu___, uu___1)) when n >= Prims.int_zero ->
           FStar_Pervasives_Native.Some n
       | uu___ -> FStar_Pervasives_Native.None in
     let dlv =
       if const_len = (FStar_Pervasives_Native.Some Prims.int_zero)
       then "1"
       else lv in
     let zero_init =
       match init.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt
           (uu___, uu___1, uu___2)) when uu___ = Prims.int_zero -> true
       | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CBool false) ->
           true
       | FStarC_Custard_Syntax.EOp
           ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufNull;
              FStarC_Custard_Syntax.po_ty = uu___;_},
            [])
           -> true
       | uu___ -> false in
     let const_init =
       match init.FStarC_Custard_Syntax.e with
       | FStarC_Custard_Syntax.EConst _0 -> true
       | uu___ -> false in
     let rec repeat n acc =
       if n <= Prims.int_zero
       then acc
       else repeat (n - Prims.int_one) (iv :: acc) in
     match (lt, const_len) with
     | (FStarC_Custard_Syntax.LStack, FStar_Pervasives_Native.Some n) when
         let uu___ =
           if scalar_elt
           then let uu___1 = FStarC_Effect.op_Bang out in uu___1 = ""
           else false in
         if uu___
         then
           ((n = Prims.int_zero) || zero_init) ||
             (const_init && (n <= init_list_max))
         else false ->
         let uu___ =
           let uu___1 =
             decl_of elt_of
               (Prims.strcat arr (Prims.strcat "[" (Prims.strcat dlv "]"))) in
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 = done_ arr in Prims.strcat " };\n" uu___5 in
               Prims.strcat
                 (if (n = Prims.int_zero) || zero_init
                  then "0"
                  else FStarC_String.concat ", " (repeat n [])) uu___4 in
             Prims.strcat " = { " uu___3 in
           Prims.strcat uu___1 uu___2 in
         Prims.strcat ind uu___
     | uu___ ->
         let alloc =
           match lt with
           | FStarC_Custard_Syntax.LStack ->
               let uu___1 =
                 let uu___2 =
                   decl_of elt_of
                     (Prims.strcat arr
                        (Prims.strcat "[" (Prims.strcat dlv "]"))) in
                 Prims.strcat uu___2 ";\n" in
               Prims.strcat ind uu___1
           | FStarC_Custard_Syntax.LHeap ->
               let uu___1 =
                 if
                   match const_len with
                   | FStar_Pervasives_Native.Some v -> true
                   | uu___2 -> false
                 then ""
                 else
                   (let n = fresh "sz" in
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = group dlv in
                            Prims.strcat uu___6
                              (Prims.strcat ";\n"
                                 (Prims.strcat ind
                                    (Prims.strcat "  if ("
                                       (Prims.strcat n
                                          (Prims.strcat
                                             " > SIZE_MAX / sizeof("
                                             (Prims.strcat elt
                                                ")) { abort(); } }\n")))))) in
                          Prims.strcat " = (size_t)" uu___5 in
                        Prims.strcat n uu___4 in
                      Prims.strcat "{ size_t " uu___3 in
                    Prims.strcat ind uu___2) in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 = group dlv in
                               Prims.strcat uu___10
                                 (Prims.strcat " * sizeof("
                                    (Prims.strcat elt
                                       (Prims.strcat "));\n"
                                          (Prims.strcat ind
                                             (Prims.strcat "if ("
                                                (Prims.strcat arr
                                                   " == NULL) { abort(); }\n")))))) in
                             Prims.strcat " *)malloc(" uu___9 in
                           Prims.strcat elt uu___8 in
                         Prims.strcat " = (" uu___7 in
                       Prims.strcat arr uu___6 in
                     Prims.strcat " *" uu___5 in
                   Prims.strcat elt uu___4 in
                 Prims.strcat ind uu___3 in
               Prims.strcat uu___1 uu___2 in
         let fill =
           if const_len = (FStar_Pervasives_Native.Some Prims.int_zero)
           then ""
           else
             (let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              if
                                len.FStarC_Custard_Syntax.ty =
                                  (FStarC_Custard_Syntax.TInt
                                     (FStarC_Const.Unsigned,
                                       FStarC_Custard_Syntax.WSizet))
                              then
                                let uu___9 = sizet_narrow () in
                                Prims.not uu___9
                              else false in
                            if uu___8
                            then group lv
                            else
                              (let uu___9 = group lv in
                               Prims.strcat "(size_t)" uu___9) in
                          Prims.strcat uu___7
                            (Prims.strcat "; "
                               (Prims.strcat i
                                  (Prims.strcat "++) {\n"
                                     (Prims.strcat ind
                                        (Prims.strcat "  "
                                           (Prims.strcat arr
                                              (Prims.strcat "["
                                                 (Prims.strcat i
                                                    (Prims.strcat "] = "
                                                       (Prims.strcat iv
                                                          (Prims.strcat ";\n"
                                                             (Prims.strcat
                                                                ind "}\n")))))))))))) in
                        Prims.strcat " < " uu___6 in
                      Prims.strcat i uu___5 in
                    Prims.strcat " = 0; " uu___4 in
                  Prims.strcat i uu___3 in
                Prims.strcat "for (size_t " uu___2 in
              Prims.strcat ind uu___1) in
         let uu___1 = FStarC_Effect.op_Bang out in
         let uu___2 =
           let uu___3 = let uu___4 = done_ arr in Prims.strcat fill uu___4 in
           Prims.strcat alloc uu___3 in
         Prims.strcat uu___1 uu___2)
and pat_tests (path : Prims.string) (t : FStarC_Custard_Syntax.cty)
  (p : FStarC_Custard_Syntax.pat) :
  (Prims.string Prims.list * (Prims.string * Prims.string) Prims.list)=
  match p with
  | FStarC_Custard_Syntax.PWild -> ([], [])
  | FStarC_Custard_Syntax.PVar x -> ([], [(x, path)])
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CString v) when
      is_string_ty t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = constant (FStarC_Custard_Syntax.CString v) in
                Prims.strcat uu___5 ") == 0" in
              Prims.strcat ", " uu___4 in
            Prims.strcat path uu___3 in
          Prims.strcat "strcmp(" uu___2 in
        [uu___1] in
      (uu___, [])
  | FStarC_Custard_Syntax.PConst c ->
      let uu___ = converted_int t t c in
      (match uu___ with
       | FStar_Pervasives_Native.Some v ->
           ([Prims.strcat path (Prims.strcat " == " v)], [])
       | FStar_Pervasives_Native.None ->
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 let uu___4 = constant c in Prims.strcat " == " uu___4 in
               Prims.strcat path uu___3 in
             [uu___2] in
           (uu___1, []))
  | FStarC_Custard_Syntax.PTuple uu___ ->
      reject "an anonymous tuple pattern"
        ["Tuples reach the backend as FStar.Pervasives.Native.MktupleN."]
  | FStarC_Custard_Syntax.POr uu___ ->
      reject "a pattern disjunction"
        ["Split the branch into one per alternative."]
  | FStarC_Custard_Syntax.PRecord (tn, fs) ->
      let uu___ = find_type tn in
      (match uu___ with
       | FStar_Pervasives_Native.Some
           { FStarC_Custard_Syntax.dt_name = uu___1;
             FStarC_Custard_Syntax.dt_params = uu___2;
             FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TRecord
               fields;
             FStarC_Custard_Syntax.dt_flags = uu___3;_}
           ->
           FStarC_List.fold_left
             (fun uu___4 uu___5 ->
                match (uu___4, uu___5) with
                | ((ts, bs), (f, q)) ->
                    let ft =
                      let uu___6 =
                        FStarC_List.tryFind
                          (fun uu___7 ->
                             match uu___7 with | (g, uu___8) -> g = f) fields in
                      match uu___6 with
                      | FStar_Pervasives_Native.Some (uu___7, ft1) -> ft1
                      | FStar_Pervasives_Native.None ->
                          FStarC_Custard_Syntax.TAny in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = c_var f in Prims.strcat "." uu___9 in
                        Prims.strcat path uu___8 in
                      pat_tests uu___7 ft q in
                    (match uu___6 with
                     | (t1, b1) ->
                         ((FStarC_List.op_At ts t1),
                           (FStarC_List.op_At bs b1)))) ([], []) fs
       | uu___1 ->
           let uu___2 =
             let uu___3 = FStarC_Custard_Syntax.string_of_name tn in
             Prims.strcat "the record type " uu___3 in
           reject uu___2
             ["It belongs to no record declaration in the program."])
  | FStarC_Custard_Syntax.PCtor (cn, ps) ->
      let uu___ = find_ctor cn in
      (match uu___ with
       | FStar_Pervasives_Native.None ->
           let uu___1 =
             let uu___2 = FStarC_Custard_Syntax.string_of_name cn in
             Prims.strcat "the constructor " uu___2 in
           reject uu___1
             ["It belongs to no type declaration in the program."]
       | FStar_Pervasives_Native.Some (d, fields) ->
           let tests =
             if single_ctor d
             then []
             else
               (let uu___1 =
                  let uu___2 = tag_of path d in
                  let uu___3 =
                    let uu___4 = c_tag cn in Prims.strcat " == " uu___4 in
                  Prims.strcat uu___2 uu___3 in
                [uu___1]) in
           let sub f =
             if single_ctor d
             then
               let uu___1 = let uu___2 = c_var f in Prims.strcat "." uu___2 in
               Prims.strcat path uu___1
             else
               (let uu___1 = arm_sel cn fields f in Prims.strcat path uu___1) in
           let rec go fs ps1 =
             match (fs, ps1) with
             | ((f, ft)::fs1, p1::ps2) ->
                 let uu___1 = let uu___2 = sub f in pat_tests uu___2 ft p1 in
                 (match uu___1 with
                  | (t1, b1) ->
                      let uu___2 = go fs1 ps2 in
                      (match uu___2 with
                       | (t2, b2) ->
                           ((FStarC_List.op_At t1 t2),
                             (FStarC_List.op_At b1 b2))))
             | uu___1 -> ([], []) in
           let uu___1 = go fields ps in
           (match uu___1 with
            | (t2, b2) -> ((FStarC_List.op_At tests t2), b2)))
and drop_indent (l : Prims.string) : Prims.string=
  let uu___ =
    if (FStarC_String.length l) > Prims.int_zero
    then
      let uu___1 = FStarC_String.substring l Prims.int_zero Prims.int_one in
      uu___1 = " "
    else false in
  if uu___
  then
    let uu___1 =
      FStarC_String.substring l Prims.int_one
        ((FStarC_String.length l) - Prims.int_one) in
    drop_indent uu___1
  else l
and brace (ind : Prims.string) (body : Prims.string) : Prims.string=
  let lines = FStarC_String.split [10] body in
  match lines with
  | ""::[] -> " { }\n"
  | l::""::[] ->
      let uu___ = let uu___1 = drop_indent l in Prims.strcat uu___1 "\n" in
      Prims.strcat " " uu___
  | uu___ -> Prims.strcat " {\n" (Prims.strcat body (Prims.strcat ind "}\n"))
and starts_with (s : Prims.string) (pre : Prims.string) : Prims.bool=
  if (FStarC_String.length s) >= (FStarC_String.length pre)
  then
    let uu___ =
      FStarC_String.substring s Prims.int_zero (FStarC_String.length pre) in
    uu___ = pre
  else false
and guard_rejected : 'a . unit -> 'a =
  fun uu___ ->
    reject "a pattern guard"
      ["Rewrite the guard as an 'if' in the branch body."]
and emit_match (ind : Prims.string) (d : dest)
  (scrut : FStarC_Custard_Syntax.expr)
  (brs : FStarC_Custard_Syntax.branch Prims.list) : Prims.string=
  let out = FStarC_Effect.mk_ref "" in
  let sv = c_expr out ind scrut in
  if match brs with | [] -> true | uu___ -> false
  then
    let uu___ = FStarC_Effect.op_Bang out in
    let uu___1 =
      let uu___2 = finish ind D_Ignore sv in
      Prims.strcat uu___2 (Prims.strcat ind "abort();\n") in
    Prims.strcat uu___ uu___1
  else
    (let direct = is_stable scrut in
     let x = if direct then sv else fresh "s" in
     let ind' = Prims.strcat ind "  " in
     let branch_body bi p b =
       let saved = FStarC_Effect.op_Bang scope in
       let uu___ = pat_tests x scrut.FStarC_Custard_Syntax.ty p in
       match uu___ with
       | (uu___1, binds) ->
           (FStarC_List.iter
              (fun uu___3 ->
                 match uu___3 with | (v, path) -> bind_alias v path) binds;
            (let body = emit bi d b in
             FStarC_Effect.op_Colon_Equals scope saved; body)) in
     let emits_nothing p b =
       let saved_ctr = FStarC_Effect.op_Bang ctr in
       let saved_declared =
         let uu___ = FStarC_Effect.op_Bang declared in FStarC_SMap.copy uu___ in
       let s = branch_body ind' p b in
       FStarC_Effect.op_Colon_Equals ctr saved_ctr;
       FStarC_Effect.op_Colon_Equals declared saved_declared;
       s = "" in
     let rec trim rbs =
       match rbs with
       | (p, uu___, b)::rest when emits_nothing p b -> trim rest
       | uu___ -> rbs in
     let kept =
       let uu___ = trim (FStarC_List.rev brs) in FStarC_List.rev uu___ in
     let all_tested = (FStarC_List.length kept) < (FStarC_List.length brs) in
     if match kept with | [] -> true | uu___ -> false
     then
       let uu___ = FStarC_Effect.op_Bang out in
       let uu___1 = finish ind D_Ignore sv in Prims.strcat uu___ uu___1
     else
       (let looked_at =
          FStarC_List.existsb
            (fun uu___ ->
               match uu___ with
               | (p, uu___1, uu___2) ->
                   let uu___3 = pat_tests x scrut.FStarC_Custard_Syntax.ty p in
                   (match uu___3 with
                    | (ts, bs) ->
                        (match ts with | hd::tl -> true | uu___4 -> false) ||
                          ((match bs with | hd::tl -> true | uu___4 -> false))))
            kept in
        if Prims.not looked_at
        then
          match kept with
          | (uu___, FStar_Pervasives_Native.None, b)::uu___1 ->
              let uu___2 = FStarC_Effect.op_Bang out in
              let uu___3 =
                let uu___4 = finish ind D_Ignore sv in
                let uu___5 = emit ind d b in Prims.strcat uu___4 uu___5 in
              Prims.strcat uu___2 uu___3
          | uu___ ->
              let uu___1 = FStarC_Effect.op_Bang out in
              let uu___2 =
                let uu___3 = finish ind D_Ignore sv in
                Prims.strcat uu___3 (Prims.strcat ind "abort();\n") in
              Prims.strcat uu___1 uu___2
        else
          (let head =
             if direct
             then FStarC_Effect.op_Bang out
             else
               (let uu___ = FStarC_Effect.op_Bang out in
                let uu___1 =
                  let uu___2 =
                    let uu___3 = decl_of scrut.FStarC_Custard_Syntax.ty x in
                    Prims.strcat uu___3
                      (Prims.strcat " = " (Prims.strcat sv ";\n")) in
                  Prims.strcat ind uu___2 in
                Prims.strcat uu___ uu___1) in
           let rec go first brs1 =
             let last p b =
               if first
               then branch_body ind p b
               else
                 (let uu___ =
                    let uu___1 =
                      let uu___2 = branch_body ind' p b in brace ind uu___2 in
                    Prims.strcat "else" uu___1 in
                  Prims.strcat ind uu___) in
             match brs1 with
             | [] -> ""
             | (p, g, b)::[] when Prims.not all_tested ->
                 (if
                    (match g with
                     | FStar_Pervasives_Native.Some v -> true
                     | uu___1 -> false)
                  then guard_rejected ()
                  else ();
                  last p b)
             | (p, g, b)::rest ->
                 (if
                    (match g with
                     | FStar_Pervasives_Native.Some v -> true
                     | uu___1 -> false)
                  then guard_rejected ()
                  else ();
                  (let uu___1 = pat_tests x scrut.FStarC_Custard_Syntax.ty p in
                   match uu___1 with
                   | (tests, uu___2) ->
                       if (match tests with | [] -> true | uu___3 -> false)
                       then last p b
                       else
                         (let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    let uu___8 = branch_body ind' p b in
                                    brace ind uu___8 in
                                  let uu___8 = go false rest in
                                  Prims.strcat uu___7 uu___8 in
                                Prims.strcat ")" uu___6 in
                              Prims.strcat
                                (FStarC_String.concat " && " tests) uu___5 in
                            Prims.strcat "if (" uu___4 in
                          Prims.strcat
                            (if first then ind else Prims.strcat ind "else ")
                            uu___3))) in
           let uu___ = go true kept in Prims.strcat head uu___)))
let rec occurs (target : Prims.string) (fuel : Prims.int)
  (t : FStarC_Custard_Syntax.cty) : Prims.bool=
  if fuel <= Prims.int_zero
  then false
  else
    (match t with
     | FStarC_Custard_Syntax.TApp (n, uu___) ->
         let uu___1 =
           let uu___2 = FStarC_Custard_Syntax.string_of_name n in
           uu___2 = target in
         if uu___1
         then true
         else
           (let uu___2 = find_type n in
            match uu___2 with
            | FStar_Pervasives_Native.Some d ->
                body_occurs target (fuel - Prims.int_one)
                  d.FStarC_Custard_Syntax.dt_body
            | FStar_Pervasives_Native.None -> false)
     | FStarC_Custard_Syntax.TTuple ts ->
         FStarC_List.existsb (occurs target (fuel - Prims.int_one)) ts
     | uu___ -> false)
and body_occurs (target : Prims.string) (fuel : Prims.int)
  (b : FStarC_Custard_Syntax.tydef) : Prims.bool=
  match b with
  | FStarC_Custard_Syntax.TAbbrev c -> occurs target fuel c
  | FStarC_Custard_Syntax.TRecord fs ->
      FStarC_List.existsb
        (fun uu___ -> match uu___ with | (uu___1, c) -> occurs target fuel c)
        fs
  | FStarC_Custard_Syntax.TVariant cs ->
      FStarC_List.existsb
        (fun uu___ ->
           match uu___ with
           | (uu___1, fs) ->
               FStarC_List.existsb
                 (fun uu___2 ->
                    match uu___2 with | (uu___3, c) -> occurs target fuel c)
                 fs) cs
  | FStarC_Custard_Syntax.TAbstract -> false
let check_finite (d : FStarC_Custard_Syntax.dtype) : unit=
  let uu___ =
    let uu___1 =
      FStarC_Custard_Syntax.string_of_name d.FStarC_Custard_Syntax.dt_name in
    body_occurs uu___1 (Prims.of_int 100) d.FStarC_Custard_Syntax.dt_body in
  if uu___
  then
    let uu___1 =
      let uu___2 =
        FStarC_Custard_Syntax.string_of_name d.FStarC_Custard_Syntax.dt_name in
      Prims.strcat "the recursive datatype " uu___2 in
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 =
            FStarC_Custard_Syntax.string_of_name
              d.FStarC_Custard_Syntax.dt_name in
          FStarC_SMap.try_find frozen_by uu___5 in
        match uu___4 with
        | FStar_Pervasives_Native.Some ext ->
            [Prims.strcat "It reaches the backend through "
               (Prims.strcat ext
                  ", whose signature mentions it.  That declaration is realized outside this program, so there is no definition of it to compile and nothing here can change the shape of the type it names.")]
        | FStar_Pervasives_Native.None -> [] in
      FStarC_List.op_At
        ["A C struct cannot contain itself by value.";
        "Use an explicit pointer (a Pulse ref, array or box) for the recursive field."]
        uu___3 in
    reject uu___1 uu___2
  else ()
let struct_tag (n : Prims.string) : Prims.string= Prims.strcat n "_s"
let enum_tag (n : Prims.string) : Prims.string= Prims.strcat n "_tags"
let is_struct (d : FStarC_Custard_Syntax.dtype) : Prims.bool=
  match d.FStarC_Custard_Syntax.dt_body with
  | FStarC_Custard_Syntax.TRecord uu___ -> true
  | FStarC_Custard_Syntax.TVariant uu___ ->
      let uu___1 = is_enum d in Prims.not uu___1
  | FStarC_Custard_Syntax.TAbbrev uu___ -> false
  | FStarC_Custard_Syntax.TAbstract -> false
let type_fwd (d : FStarC_Custard_Syntax.dtype) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = builtin_type d.FStarC_Custard_Syntax.dt_name in
    match uu___1 with
    | FStar_Pervasives_Native.Some v -> true
    | uu___2 -> false in
  if uu___
  then FStar_Pervasives_Native.None
  else
    (let uu___1 = is_struct d in
     if uu___1
     then
       let n = c_name d.FStarC_Custard_Syntax.dt_name in
       FStar_Pervasives_Native.Some
         (Prims.strcat "typedef struct "
            (Prims.strcat (struct_tag n)
               (Prims.strcat " " (Prims.strcat n ";\n"))))
     else FStar_Pervasives_Native.None)
let rec value_deps (t : FStarC_Custard_Syntax.cty) : Prims.string Prims.list=
  match t with
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ = FStarC_Custard_Syntax.string_of_name n in
      let uu___1 = FStarC_List.collect value_deps args in uu___ :: uu___1
  | FStarC_Custard_Syntax.TTuple ts -> FStarC_List.collect value_deps ts
  | FStarC_Custard_Syntax.TBuf uu___ -> []
  | FStarC_Custard_Syntax.TRef uu___ -> []
  | FStarC_Custard_Syntax.TArrow uu___ -> []
  | uu___ -> []
let body_value_deps (b : FStarC_Custard_Syntax.tydef) :
  Prims.string Prims.list=
  match b with
  | FStarC_Custard_Syntax.TAbbrev c -> value_deps c
  | FStarC_Custard_Syntax.TRecord fs ->
      FStarC_List.collect
        (fun uu___ -> match uu___ with | (uu___1, c) -> value_deps c) fs
  | FStarC_Custard_Syntax.TVariant cs ->
      FStarC_List.collect
        (fun uu___ ->
           match uu___ with
           | (uu___1, fs) ->
               FStarC_List.collect
                 (fun uu___2 ->
                    match uu___2 with | (uu___3, c) -> value_deps c) fs) cs
  | FStarC_Custard_Syntax.TAbstract -> []
let sort_types (ds : FStarC_Custard_Syntax.dtype Prims.list) :
  FStarC_Custard_Syntax.dtype Prims.list=
  let index = FStarC_SMap.create (Prims.of_int 64) in
  FStarC_List.iter
    (fun d ->
       let uu___1 =
         FStarC_Custard_Syntax.string_of_name d.FStarC_Custard_Syntax.dt_name in
       FStarC_SMap.add index uu___1 d) ds;
  (let out = FStarC_Effect.mk_ref [] in
   let seen = FStarC_SMap.create (Prims.of_int 64) in
   let busy = FStarC_SMap.create (Prims.of_int 64) in
   let rec visit d =
     let k =
       FStarC_Custard_Syntax.string_of_name d.FStarC_Custard_Syntax.dt_name in
     let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_SMap.try_find seen k in
         match uu___3 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___4 -> false in
       if uu___2
       then true
       else
         (let uu___3 = FStarC_SMap.try_find busy k in
          match uu___3 with
          | FStar_Pervasives_Native.Some v -> true
          | uu___4 -> false) in
     if uu___1
     then ()
     else
       (FStarC_SMap.add busy k true;
        (let uu___4 = body_value_deps d.FStarC_Custard_Syntax.dt_body in
         FStarC_List.iter
           (fun n ->
              let uu___5 = FStarC_SMap.try_find index n in
              match uu___5 with
              | FStar_Pervasives_Native.Some d' -> visit d'
              | FStar_Pervasives_Native.None -> ()) uu___4);
        FStarC_SMap.remove busy k;
        FStarC_SMap.add seen k true;
        (let uu___6 = let uu___7 = FStarC_Effect.op_Bang out in d :: uu___7 in
         FStarC_Effect.op_Colon_Equals out uu___6)) in
   FStarC_List.iter visit ds;
   (let uu___2 = FStarC_Effect.op_Bang out in FStarC_List.rev uu___2))
let type_decl (d : FStarC_Custard_Syntax.dtype) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = builtin_type d.FStarC_Custard_Syntax.dt_name in
    match uu___1 with
    | FStar_Pervasives_Native.Some v -> true
    | uu___2 -> false in
  if uu___
  then FStar_Pervasives_Native.None
  else
    (let n = c_name d.FStarC_Custard_Syntax.dt_name in
     let open_struct uu___1 =
       Prims.strcat "struct " (Prims.strcat (struct_tag n) " {\n") in
     match d.FStarC_Custard_Syntax.dt_body with
     | FStarC_Custard_Syntax.TAbstract -> FStar_Pervasives_Native.None
     | FStarC_Custard_Syntax.TAbbrev c ->
         let uu___1 =
           let uu___2 = let uu___3 = decl_of c n in Prims.strcat uu___3 ";\n" in
           Prims.strcat "typedef " uu___2 in
         FStar_Pervasives_Native.Some uu___1
     | FStarC_Custard_Syntax.TRecord fs ->
         (check_finite d;
          (let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   FStarC_List.map
                     (fun uu___6 ->
                        match uu___6 with
                        | (f, c) ->
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = c_var f in decl_of c uu___9 in
                              Prims.strcat uu___8 ";\n" in
                            Prims.strcat "  " uu___7) fs in
                 FStarC_String.concat "" uu___5 in
               Prims.strcat uu___4 "};\n" in
             Prims.strcat (open_struct ()) uu___3 in
           FStar_Pervasives_Native.Some uu___2))
     | FStarC_Custard_Syntax.TVariant cs ->
         (check_finite d;
          (let uu___2 = is_enum d in
           if uu___2
           then
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     FStarC_List.map
                       (fun uu___7 ->
                          match uu___7 with
                          | (c, uu___8) ->
                              let uu___9 = c_tag c in
                              Prims.strcat "  " uu___9) cs in
                   FStarC_String.concat ",\n" uu___6 in
                 Prims.strcat uu___5
                   (Prims.strcat "\n} " (Prims.strcat n ";\n")) in
               Prims.strcat "typedef enum {\n" uu___4 in
             FStar_Pervasives_Native.Some uu___3
           else
             if single_ctor d
             then
               (let uu___3 = FStarC_List.hd cs in
                match uu___3 with
                | (uu___4, fs) ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStarC_List.map
                              (fun uu___9 ->
                                 match uu___9 with
                                 | (f, c) ->
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 = c_var f in
                                         decl_of c uu___12 in
                                       Prims.strcat uu___11 ";\n" in
                                     Prims.strcat "  " uu___10) fs in
                          FStarC_String.concat "" uu___8 in
                        Prims.strcat uu___7 "};\n" in
                      Prims.strcat (open_struct ()) uu___6 in
                    FStar_Pervasives_Native.Some uu___5)
             else
               (let nonempty =
                  FStarC_List.filter
                    (fun uu___3 ->
                       match uu___3 with
                       | (uu___4, fs) ->
                           (match fs with | hd::tl -> true | uu___5 -> false))
                    cs in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStarC_List.map
                              (fun uu___9 ->
                                 match uu___9 with
                                 | (c, uu___10) ->
                                     let uu___11 = c_tag c in
                                     Prims.strcat "  " uu___11) cs in
                          FStarC_String.concat ",\n" uu___8 in
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                let uu___12 =
                                  let uu___13 =
                                    let uu___14 =
                                      match nonempty with
                                      | [] -> ""
                                      | uu___15 ->
                                          let uu___16 =
                                            let uu___17 =
                                              let uu___18 =
                                                FStarC_List.map
                                                  (fun uu___19 ->
                                                     match uu___19 with
                                                     | (c, fs) ->
                                                         if arm_flat fs
                                                         then
                                                           let uu___20 =
                                                             let uu___21 =
                                                               let uu___22 =
                                                                 arm_name c in
                                                               decl_of
                                                                 (FStar_Pervasives_Native.snd
                                                                    (
                                                                    FStarC_List.hd
                                                                    fs))
                                                                 uu___22 in
                                                             Prims.strcat
                                                               uu___21 ";\n" in
                                                           Prims.strcat
                                                             "    " uu___20
                                                         else
                                                           (let uu___20 =
                                                              let uu___21 =
                                                                let uu___22 =
                                                                  FStarC_List.map
                                                                    (
                                                                    fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    (f, t) ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    = c_var f in
                                                                    decl_of t
                                                                    uu___26 in
                                                                    Prims.strcat
                                                                    uu___25
                                                                    ";\n" in
                                                                    Prims.strcat
                                                                    "      "
                                                                    uu___24)
                                                                    fs in
                                                                FStarC_String.concat
                                                                  "" uu___22 in
                                                              let uu___22 =
                                                                let uu___23 =
                                                                  let uu___24
                                                                    =
                                                                    arm_name
                                                                    c in
                                                                  Prims.strcat
                                                                    uu___24
                                                                    ";\n" in
                                                                Prims.strcat
                                                                  "    } "
                                                                  uu___23 in
                                                              Prims.strcat
                                                                uu___21
                                                                uu___22 in
                                                            Prims.strcat
                                                              "    struct {\n"
                                                              uu___20))
                                                  nonempty in
                                              FStarC_String.concat "" uu___18 in
                                            Prims.strcat uu___17 "  } val;\n" in
                                          Prims.strcat "  union {\n" uu___16 in
                                    Prims.strcat uu___14 "};\n" in
                                  Prims.strcat " tag;\n" uu___13 in
                                Prims.strcat (enum_tag n) uu___12 in
                              Prims.strcat "  enum " uu___11 in
                            Prims.strcat (open_struct ()) uu___10 in
                          Prims.strcat "\n};\n" uu___9 in
                        Prims.strcat uu___7 uu___8 in
                      Prims.strcat " {\n" uu___6 in
                    Prims.strcat (enum_tag n) uu___5 in
                  Prims.strcat "enum " uu___4 in
                FStar_Pervasives_Native.Some uu___3))))
let kept_binders (l : FStarC_Custard_Syntax.dlet) :
  FStarC_Custard_Syntax.binder Prims.list=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang keeps in
    let uu___2 =
      FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | FStar_Pervasives_Native.Some flags ->
      filter_by flags l.FStarC_Custard_Syntax.dl_binders
  | FStar_Pervasives_Native.None -> l.FStarC_Custard_Syntax.dl_binders
let signature (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  let args =
    let uu___ = kept_binders l in
    match uu___ with
    | [] -> "void"
    | bs ->
        let uu___1 =
          FStarC_List.map
            (fun b ->
               let uu___2 = lookup_var b.FStarC_Custard_Syntax.b_name in
               decl_of b.FStarC_Custard_Syntax.b_ty uu___2) bs in
        FStarC_String.concat ", " uu___1 in
  let hd =
    let uu___ = c_name l.FStarC_Custard_Syntax.dl_name in
    Prims.strcat uu___ (Prims.strcat "(" (Prims.strcat args ")")) in
  if
    match l.FStarC_Custard_Syntax.dl_ret with
    | FStarC_Custard_Syntax.TUnit -> true
    | uu___ -> false
  then Prims.strcat "void " hd
  else decl_of l.FStarC_Custard_Syntax.dl_ret hd
let const_op (o : FStarC_Custard_Syntax.prim_op) : Prims.bool=
  (match o.FStarC_Custard_Syntax.po_ty with
   | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat uu___) ->
       false
   | uu___ -> true) &&
    (match o.FStarC_Custard_Syntax.po_op with
     | FStarC_Custard_Syntax.Add -> true
     | FStarC_Custard_Syntax.AddW -> true
     | FStarC_Custard_Syntax.Sub -> true
     | FStarC_Custard_Syntax.SubW -> true
     | FStarC_Custard_Syntax.Mult -> true
     | FStarC_Custard_Syntax.MultW -> true
     | FStarC_Custard_Syntax.Div -> true
     | FStarC_Custard_Syntax.DivW -> true
     | FStarC_Custard_Syntax.Mod -> true
     | FStarC_Custard_Syntax.BOr -> true
     | FStarC_Custard_Syntax.BAnd -> true
     | FStarC_Custard_Syntax.BXor -> true
     | FStarC_Custard_Syntax.BShiftL -> true
     | FStarC_Custard_Syntax.BShiftR -> true
     | FStarC_Custard_Syntax.BNot -> true
     | FStarC_Custard_Syntax.Eq -> true
     | FStarC_Custard_Syntax.Neq -> true
     | FStarC_Custard_Syntax.Lt -> true
     | FStarC_Custard_Syntax.Lte -> true
     | FStarC_Custard_Syntax.Gt -> true
     | FStarC_Custard_Syntax.Gte -> true
     | FStarC_Custard_Syntax.And -> true
     | FStarC_Custard_Syntax.Or -> true
     | FStarC_Custard_Syntax.Not -> true
     | uu___ -> false)
let rec static_init (x : FStarC_Custard_Syntax.expr) :
  Prims.string FStar_Pervasives_Native.option=
  match x.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst c ->
      let uu___ =
        converted_int x.FStarC_Custard_Syntax.ty x.FStarC_Custard_Syntax.ty c in
      (match uu___ with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None ->
           (match c with
            | FStarC_Custard_Syntax.CInt
                (uu___1, uu___2, FStar_Pervasives_Native.None) ->
                FStar_Pervasives_Native.None
            | FStarC_Custard_Syntax.CFloat (v, fw) when narrow_ty fw ->
                let uu___1 = narrow_float_init fw v in
                FStar_Pervasives_Native.Some uu___1
            | uu___1 ->
                let uu___2 = constant c in
                FStar_Pervasives_Native.Some uu___2))
  | FStarC_Custard_Syntax.EQual (n, uu___) when
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang macros in
        let uu___3 = FStarC_Custard_Syntax.string_of_name n in
        FStarC_SMap.try_find uu___2 uu___3 in
      match uu___1 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___2 -> false ->
      let uu___1 = c_name n in FStar_Pervasives_Native.Some uu___1
  | FStarC_Custard_Syntax.ECast (e1, t) ->
      let uu___ =
        let uu___1 = static_init e1 in
        ((e1.FStarC_Custard_Syntax.ty), t, uu___1) in
      (match uu___ with
       | (FStarC_Custard_Syntax.TInt a, FStarC_Custard_Syntax.TInt b,
          FStar_Pervasives_Native.Some v) when a = b ->
           FStar_Pervasives_Native.Some v
       | (uu___1, FStarC_Custard_Syntax.TFloat fw, uu___2) when narrow_ty fw
           -> FStar_Pervasives_Native.None
       | (FStarC_Custard_Syntax.TFloat fw, uu___1, uu___2) when narrow_ty fw
           -> FStar_Pervasives_Native.None
       | (uu___1, uu___2, FStar_Pervasives_Native.Some v) ->
           let uu___3 =
             let uu___4 =
               let uu___5 = ty t in Prims.strcat uu___5 (Prims.strcat ")" v) in
             Prims.strcat "(" uu___4 in
           FStar_Pervasives_Native.Some uu___3
       | uu___1 -> FStar_Pervasives_Native.None)
  | FStarC_Custard_Syntax.ECoerce (e1, t) ->
      let uu___ = static_init e1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some v ->
           if e1.FStarC_Custard_Syntax.ty = t
           then FStar_Pervasives_Native.Some v
           else
             (let uu___1 =
                let uu___2 =
                  let uu___3 = ty t in
                  Prims.strcat uu___3 (Prims.strcat ")" v) in
                Prims.strcat "(" uu___2 in
              FStar_Pervasives_Native.Some uu___1)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufNull;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       [])
      ->
      let uu___1 =
        let uu___2 =
          let uu___3 = ty x.FStarC_Custard_Syntax.ty in
          Prims.strcat uu___3 ")NULL" in
        Prims.strcat "(" uu___2 in
      FStar_Pervasives_Native.Some uu___1
  | FStarC_Custard_Syntax.EOp (o, es) when
      let uu___ = const_op o in
      if uu___
      then
        FStarC_List.for_all
          (fun a ->
             let uu___1 =
               let uu___2 = static_init a in
               match uu___2 with
               | FStar_Pervasives_Native.Some v -> true
               | uu___3 -> false in
             if uu___1
             then
               let uu___2 = is_string_ty a.FStarC_Custard_Syntax.ty in
               Prims.not uu___2
             else false) es
      else false ->
      let out = FStarC_Effect.mk_ref "" in
      let v = c_expr out "" x in
      let uu___ = let uu___1 = FStarC_Effect.op_Bang out in uu___1 = "" in
      if uu___
      then FStar_Pervasives_Native.Some v
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let has_static_init (l : FStarC_Custard_Syntax.dlet) : Prims.bool=
  (let uu___1 =
     FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
   FStarC_Effect.op_Colon_Equals current uu___1);
  (let uu___1 = static_init l.FStarC_Custard_Syntax.dl_body in
   match uu___1 with
   | FStar_Pervasives_Native.Some v -> true
   | uu___2 -> false)
let array_decl (l : FStarC_Custard_Syntax.dlet) :
  Prims.string FStar_Pervasives_Native.option=
  match (((l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e),
          (l.FStarC_Custard_Syntax.dl_ret))
  with
  | (FStarC_Custard_Syntax.EOp
     ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
        FStarC_Custard_Syntax.po_ty = uu___;_},
      elems),
     FStarC_Custard_Syntax.TBuf t) ->
      let out = FStarC_Effect.mk_ref "" in
      let vs = FStarC_List.map (fun x -> c_rvalue out "" t x) elems in
      if (match elems with | [] -> true | uu___1 -> false)
      then
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStarC_Custard_Syntax.string_of_name
                    l.FStarC_Custard_Syntax.dl_name in
                Prims.strcat uu___5
                  " is an empty static array, and C has no declaration for one." in
              Prims.strcat "Custard: " uu___4 in
            FStarC_Errors_Msg.text uu___3 in
          [uu___2;
          FStarC_Errors_Msg.text
            "An array object needs at least one element, and a run with no elements has no address to hand out either.";
          FStarC_Errors_Msg.text
            "Use Pulse.Lib.Array.null if what is meant is the absence of a run."] in
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Error_CustardBadStaticArray ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___1)
      else
        (let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 = c_name l.FStarC_Custard_Syntax.dl_name in
                 Prims.strcat uu___5
                   (Prims.strcat "["
                      (Prims.strcat
                         (Prims.string_of_int (FStarC_List.length elems)) "]")) in
               decl_of t uu___4 in
             Prims.strcat uu___3
               (Prims.strcat " = { "
                  (Prims.strcat (FStarC_String.concat ", " vs) " };\n")) in
           Prims.strcat "const " uu___2 in
         FStar_Pervasives_Native.Some uu___1)
  | uu___ -> FStar_Pervasives_Native.None
let array_extern (l : FStarC_Custard_Syntax.dlet) :
  Prims.string FStar_Pervasives_Native.option=
  match (((l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e),
          (l.FStarC_Custard_Syntax.dl_ret))
  with
  | (FStarC_Custard_Syntax.EOp
     ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
        FStarC_Custard_Syntax.po_ty = uu___;_},
      elems),
     FStarC_Custard_Syntax.TBuf t) when
      match elems with | hd::tl -> true | uu___1 -> false ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = c_name l.FStarC_Custard_Syntax.dl_name in
              Prims.strcat uu___5
                (Prims.strcat "["
                   (Prims.strcat
                      (Prims.string_of_int (FStarC_List.length elems)) "]")) in
            decl_of t uu___4 in
          Prims.strcat uu___3 ";\n" in
        Prims.strcat "extern const " uu___2 in
      FStar_Pervasives_Native.Some uu___1
  | uu___ -> FStar_Pervasives_Native.None
let is_static_array (l : FStarC_Custard_Syntax.dlet) : Prims.bool=
  match (l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      -> true
  | uu___ -> false
let global_decl (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  (let uu___1 =
     FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
   FStarC_Effect.op_Colon_Equals current uu___1);
  (let uu___1 = array_decl l in
   match uu___1 with
   | FStar_Pervasives_Native.Some d -> d
   | FStar_Pervasives_Native.None ->
       let d =
         let uu___2 = c_name l.FStarC_Custard_Syntax.dl_name in
         decl_of l.FStarC_Custard_Syntax.dl_ret uu___2 in
       let uu___2 = static_init l.FStarC_Custard_Syntax.dl_body in
       (match uu___2 with
        | FStar_Pervasives_Native.Some v ->
            Prims.strcat d (Prims.strcat " = " (Prims.strcat v ";\n"))
        | FStar_Pervasives_Native.None -> Prims.strcat d ";\n"))
let is_macro (l : FStarC_Custard_Syntax.dlet) : Prims.bool=
  if
    match l.FStarC_Custard_Syntax.dl_binders with
    | [] -> true
    | uu___ -> false
  then
    FStarC_List.existsb FStarC_Custard_Syntax.uu___is_CMacro
      l.FStarC_Custard_Syntax.dl_flags
  else false
let macro_value (l : FStarC_Custard_Syntax.dlet) :
  Prims.string FStar_Pervasives_Native.option=
  match (l.FStarC_Custard_Syntax.dl_body).FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt
      (v, b, FStar_Pervasives_Native.Some sw)) ->
      let uu___ = int_literal sw v b in FStar_Pervasives_Native.Some uu___
  | uu___ -> static_init l.FStarC_Custard_Syntax.dl_body
let macro_decl (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  (let uu___1 =
     FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
   FStarC_Effect.op_Colon_Equals current uu___1);
  (let uu___1 = macro_value l in
   match uu___1 with
   | FStar_Pervasives_Native.Some v ->
       let uu___2 =
         let uu___3 = c_name l.FStarC_Custard_Syntax.dl_name in
         Prims.strcat uu___3 (Prims.strcat " (" (Prims.strcat v ")\n")) in
       Prims.strcat "#define " uu___2
   | FStar_Pervasives_Native.None ->
       let uu___2 =
         let uu___3 =
           let uu___4 =
             let uu___5 =
               let uu___6 =
                 FStarC_Custard_Syntax.string_of_name
                   l.FStarC_Custard_Syntax.dl_name in
               Prims.strcat uu___6
                 " is marked [@@ CMacro ] but its value is not a constant expression." in
             Prims.strcat "Custard: " uu___5 in
           FStarC_Errors_Msg.text uu___4 in
         [uu___3;
         FStarC_Errors_Msg.text
           "A [#define] is substituted before the program runs, so there is nothing to evaluate it: only a literal, or a cast or an arithmetic combination of literals, can be one.";
         FStarC_Errors_Msg.text
           "Drop the attribute to get an ordinary variable, initialized at startup like any other global."] in
       FStarC_Errors.raise_error0 FStarC_Errors_Codes.Error_CustardBadMacro
         () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic uu___2))
let global_init (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  (let uu___1 =
     FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
   FStarC_Effect.op_Colon_Equals current uu___1);
  FStarC_Effect.op_Colon_Equals ctr Prims.int_zero;
  FStarC_Effect.op_Colon_Equals void_ret false;
  reset_scope ();
  (let uu___4 =
     let uu___5 = c_name l.FStarC_Custard_Syntax.dl_name in D_Assign uu___5 in
   emit "  " uu___4 l.FStarC_Custard_Syntax.dl_body)
let let_decl (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  (let uu___1 =
     FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
   FStarC_Effect.op_Colon_Equals current uu___1);
  FStarC_Effect.op_Colon_Equals ctr Prims.int_zero;
  FStarC_Effect.op_Colon_Equals void_ret
    (match l.FStarC_Custard_Syntax.dl_ret with
     | FStarC_Custard_Syntax.TUnit -> true
     | uu___3 -> false);
  reset_scope ();
  (let uu___5 = kept_binders l in
   FStarC_List.iter
     (fun b -> let uu___6 = bind_var b.FStarC_Custard_Syntax.b_name in ())
     uu___5);
  FStarC_List.iter
    (fun b ->
       if
         match b.FStarC_Custard_Syntax.b_ty with
         | FStarC_Custard_Syntax.TUnit -> true
         | uu___6 -> false
       then bind_alias b.FStarC_Custard_Syntax.b_name unit_value
       else ()) l.FStarC_Custard_Syntax.dl_binders;
  if
    (match l.FStarC_Custard_Syntax.dl_binders with
     | [] -> true
     | uu___7 -> false)
  then
    (let uu___7 =
       let uu___8 =
         FStarC_Custard_Syntax.string_of_name l.FStarC_Custard_Syntax.dl_name in
       Prims.strcat "the top-level value " uu___8 in
     reject uu___7
       ["C has no way to initialize a global from a computation.";
       "Make it a function of unit."])
  else ();
  (let used = vars_of l.FStarC_Custard_Syntax.dl_body in
   let voids =
     let uu___7 =
       let uu___8 = kept_binders l in
       FStarC_List.collect
         (fun b ->
            let uu___9 =
              FStarC_List.existsb
                (fun y -> y = b.FStarC_Custard_Syntax.b_name) used in
            if uu___9
            then []
            else
              (let uu___10 =
                 let uu___11 =
                   let uu___12 = lookup_var b.FStarC_Custard_Syntax.b_name in
                   Prims.strcat uu___12 ";\n" in
                 Prims.strcat "  (void)" uu___11 in
               [uu___10])) uu___8 in
     FStarC_String.concat "" uu___7 in
   let uu___7 = signature l in
   let uu___8 =
     let uu___9 =
       let uu___10 =
         let uu___11 = emit "  " D_Return l.FStarC_Custard_Syntax.dl_body in
         Prims.strcat uu___11 "}\n" in
       Prims.strcat voids uu___10 in
     Prims.strcat " {\n" uu___9 in
   Prims.strcat uu___7 uu___8)
let rec arg_ctys (t : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.cty Prims.list=
  match t with
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = arg_ctys b in a :: uu___1
  | uu___ -> []
let rec ret_cty (t : FStarC_Custard_Syntax.cty) : FStarC_Custard_Syntax.cty=
  match t with
  | FStarC_Custard_Syntax.TArrow (uu___, uu___1, b) -> ret_cty b
  | uu___ -> t
let is_c_identifier (s : Prims.string) : Prims.bool=
  if s <> ""
  then
    FStarC_List.for_all
      (fun c ->
         let n = FStar_Char.int_of_char c in
         ((((n >= (Prims.of_int 0x41)) && (n <= (Prims.of_int 0x5a))) ||
             ((n >= (Prims.of_int 0x61)) && (n <= (Prims.of_int 0x7a))))
            || ((n >= (Prims.of_int 0x30)) && (n <= (Prims.of_int 0x39))))
           || (n = (Prims.of_int 0x5f))) (FStarC_String.list_of_string s)
  else false
let extern_decl (x : FStarC_Custard_Syntax.dexternal) :
  Prims.string FStar_Pervasives_Native.option=
  if
    match x.FStarC_Custard_Syntax.dx_header with
    | FStar_Pervasives_Native.Some v -> true
    | uu___ -> false
  then FStar_Pervasives_Native.None
  else
    ((match x.FStarC_Custard_Syntax.dx_target with
      | FStar_Pervasives_Native.Some t when
          let uu___1 = is_c_identifier t in Prims.not uu___1 ->
          ((let uu___2 =
              FStarC_Custard_Syntax.string_of_name
                x.FStarC_Custard_Syntax.dx_name in
            FStarC_Effect.op_Colon_Equals current uu___2);
           reject (Prims.strcat "the external name `" (Prims.strcat t "'"))
             ["It is not a C identifier, so Custard cannot declare it, and                  no [@@custard_c_header] says which header does.";
             "Add [@@custard_c_header \"...\"] beside the                  [@@custard_extern] naming the header that declares it."])
      | uu___1 -> ());
     (match () with
      | () ->
          let nm = emitted_name (FStarC_Custard_Syntax.DExternal x) in
          ((let uu___2 =
              FStarC_Custard_Syntax.string_of_name
                x.FStarC_Custard_Syntax.dx_name in
            FStarC_Effect.op_Colon_Equals current uu___2);
           (let rec spine t acc =
              match t with
              | FStarC_Custard_Syntax.TArrow (a, uu___2, b) ->
                  spine b (a :: acc)
              | uu___2 ->
                  (match acc with
                   | [] -> FStar_Pervasives_Native.None
                   | uu___3 ->
                       FStar_Pervasives_Native.Some
                         ((FStarC_List.rev acc), t)) in
            let uu___2 = spine x.FStarC_Custard_Syntax.dx_ty [] in
            match uu___2 with
            | FStar_Pervasives_Native.Some (args, ret) ->
                let args1 =
                  FStarC_List.filter
                    (fun a ->
                       Prims.not
                         (match a with
                          | FStarC_Custard_Syntax.TUnit -> true
                          | uu___3 -> false)) args in
                let params =
                  match args1 with
                  | [] -> "void"
                  | uu___3 ->
                      let uu___4 = FStarC_List.map ty args1 in
                      FStarC_String.concat ", " uu___4 in
                let hd =
                  Prims.strcat nm
                    (Prims.strcat "(" (Prims.strcat params ")")) in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      if
                        match ret with
                        | FStarC_Custard_Syntax.TUnit -> true
                        | uu___6 -> false
                      then Prims.strcat "void " hd
                      else decl_of ret hd in
                    Prims.strcat uu___5 ";\n" in
                  Prims.strcat "extern " uu___4 in
                FStar_Pervasives_Native.Some uu___3
            | FStar_Pervasives_Native.None ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = decl_of x.FStarC_Custard_Syntax.dx_ty nm in
                    Prims.strcat uu___5 ";\n" in
                  Prims.strcat "extern " uu___4 in
                FStar_Pervasives_Native.Some uu___3))))
let rec dedup (xs : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> []
  | x::rest ->
      let uu___ =
        let uu___1 = FStarC_List.filter (fun y -> y <> x) rest in
        dedup uu___1 in
      x :: uu___
let trim_nl (s : Prims.string) : Prims.string=
  let n = FStarC_String.length s in
  let uu___ =
    if n > Prims.int_zero
    then
      let uu___1 =
        FStarC_String.substring s (n - Prims.int_one) Prims.int_one in
      uu___1 = "\n"
    else false in
  if uu___
  then FStarC_String.substring s Prims.int_zero (n - Prims.int_one)
  else s
let no_unit : unit_info=
  {
    cu_name = FStar_Pervasives_Native.None;
    cu_headers = [];
    cu_inits = [];
    cu_no_prefix = []
  }
let init_name (cu : unit_info) : Prims.string=
  match cu.cu_name with
  | FStar_Pervasives_Native.Some u ->
      let uu___ = sanitize u in Prims.strcat uu___ "_init_globals"
  | FStar_Pervasives_Native.None -> "custard_init_globals"
let local (d : FStarC_Custard_Syntax.decl) : Prims.bool=
  let uu___ = FStarC_Custard_Syntax.imported_unit d in
  match uu___ with | FStar_Pervasives_Native.None -> true | uu___1 -> false
let global_inits_of (p : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.dlet Prims.list=
  FStarC_List.collect
    (fun d ->
       let uu___ = let uu___1 = local d in Prims.not uu___1 in
       if uu___
       then []
       else
         (match d with
          | FStarC_Custard_Syntax.DLet l when
              let uu___1 =
                let uu___2 =
                  if
                    match l.FStarC_Custard_Syntax.dl_binders with
                    | [] -> true
                    | uu___3 -> false
                  then let uu___3 = is_macro l in Prims.not uu___3
                  else false in
                if uu___2
                then let uu___3 = has_static_init l in Prims.not uu___3
                else false in
              if uu___1
              then let uu___2 = is_static_array l in Prims.not uu___2
              else false -> [l]
          | uu___1 -> [])) p
let init_globals_name (cu : unit_info) (p : FStarC_Custard_Syntax.program) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = global_inits_of p in
    match uu___1 with | hd::tl -> true | uu___2 -> false in
  if uu___
  then let uu___1 = init_name cu in FStar_Pervasives_Native.Some uu___1
  else FStar_Pervasives_Native.None
let is_public (l : FStarC_Custard_Syntax.dlet) : Prims.bool=
  let uu___ =
    let uu___1 =
      FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Root
        l.FStarC_Custard_Syntax.dl_flags in
    if uu___1
    then
      let uu___2 =
        FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Entrypoint
          l.FStarC_Custard_Syntax.dl_flags in
      Prims.not uu___2
    else false in
  if uu___
  then
    let uu___1 =
      FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Private
        l.FStarC_Custard_Syntax.dl_flags in
    Prims.not uu___1
  else false
let storage (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  let uu___ = is_public l in if uu___ then "" else "static "
let prologue_of (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  let uu___ =
    FStarC_List.collect
      (fun uu___1 ->
         match uu___1 with
         | FStarC_Custard_Syntax.Prologue s -> [Prims.strcat s "\n"]
         | uu___2 -> []) l.FStarC_Custard_Syntax.dl_flags in
  FStarC_String.concat "" uu___
let epilogue_of (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  let uu___ =
    FStarC_List.collect
      (fun uu___1 ->
         match uu___1 with
         | FStarC_Custard_Syntax.Epilogue s -> [Prims.strcat s "\n"]
         | uu___2 -> []) l.FStarC_Custard_Syntax.dl_flags in
  FStarC_String.concat "" uu___
let inline_of (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  let uu___ =
    FStarC_List.existsb FStarC_Custard_Syntax.uu___is_CInline
      l.FStarC_Custard_Syntax.dl_flags in
  if uu___ then "inline " else ""
let comment_of (l : FStarC_Custard_Syntax.dlet) : Prims.string=
  let uu___ =
    FStarC_List.collect
      (fun uu___1 ->
         match uu___1 with
         | FStarC_Custard_Syntax.Comment c ->
             [Prims.strcat "/* " (Prims.strcat c " */\n")]
         | uu___2 -> []) l.FStarC_Custard_Syntax.dl_flags in
  FStarC_String.concat "" uu___
let build_renames (extra : Prims.string Prims.list)
  (p : FStarC_Custard_Syntax.program) : unit=
  let mods =
    let uu___ = FStarC_Options.custard_c_no_prefix () in
    FStarC_List.op_At uu___ extra in
  (let uu___1 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals renames uu___1);
  if (match mods with | [] -> true | uu___1 -> false)
  then ()
  else
    (let taken = FStarC_SMap.create (Prims.of_int 50) in
     FStarC_List.iter
       (fun d ->
          let n = FStarC_Custard_Syntax.name_of_decl d in
          let uu___2 =
            let uu___3 = extern_target d in
            match uu___3 with
            | FStar_Pervasives_Native.Some t -> t
            | FStar_Pervasives_Native.None ->
                let uu___4 =
                  let uu___5 = FStarC_Custard_Syntax.mangled_name n in
                  sanitize uu___5 in
                escape_kw uu___4 in
          let uu___3 = FStarC_Custard_Syntax.string_of_name n in
          FStarC_SMap.add taken uu___2 uu___3) p;
     (let claimed = FStarC_SMap.create (Prims.of_int 20) in
      let used_mod = FStarC_SMap.create (Prims.of_int 5) in
      let renamable d =
        match d with
        | FStarC_Custard_Syntax.DLet l ->
            let uu___2 = is_public l in
            if uu___2
            then
              FStar_Pervasives_Native.Some (l.FStarC_Custard_Syntax.dl_name)
            else FStar_Pervasives_Native.None
        | FStarC_Custard_Syntax.DType t ->
            FStar_Pervasives_Native.Some (t.FStarC_Custard_Syntax.dt_name)
        | FStarC_Custard_Syntax.DExternal x ->
            (match x.FStarC_Custard_Syntax.dx_target with
             | FStar_Pervasives_Native.Some "" ->
                 FStar_Pervasives_Native.Some
                   (x.FStarC_Custard_Syntax.dx_name)
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some
                   (x.FStarC_Custard_Syntax.dx_name)
             | FStar_Pervasives_Native.Some uu___2 ->
                 FStar_Pervasives_Native.None)
        | uu___2 -> FStar_Pervasives_Native.None in
      let ctors_of d =
        match d with
        | FStarC_Custard_Syntax.DType
            { FStarC_Custard_Syntax.dt_name = uu___2;
              FStarC_Custard_Syntax.dt_params = uu___3;
              FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TVariant
                cs;
              FStarC_Custard_Syntax.dt_flags = uu___4;_}
            -> FStarC_List.map FStar_Pervasives_Native.fst cs
        | uu___2 -> [] in
      (let uu___3 =
         FStarC_List.collect
           (fun d ->
              let uu___4 = renamable d in
              match uu___4 with
              | FStar_Pervasives_Native.Some n ->
                  let uu___5 =
                    let uu___6 = ctors_of d in
                    FStarC_List.map (fun c -> (c, d)) uu___6 in
                  (n, d) :: uu___5
              | FStar_Pervasives_Native.None -> []) p in
       FStarC_List.iter
         (fun uu___4 ->
            match uu___4 with
            | (dn, uu___5) ->
                (match () with
                 | uu___6 when
                     match dn.FStarC_Custard_Syntax.spec with
                     | FStar_Pervasives_Native.None -> true
                     | uu___7 -> false ->
                     let m =
                       FStarC_String.concat "." dn.FStarC_Custard_Syntax.ns in
                     let uu___7 = FStarC_List.existsb (fun x -> x = m) mods in
                     if uu___7
                     then
                       (FStarC_SMap.add used_mod m true;
                        (let tgt =
                           let uu___9 = sanitize dn.FStarC_Custard_Syntax.id in
                           escape_kw uu___9 in
                         let src = FStarC_Custard_Syntax.string_of_name dn in
                         (let uu___10 = FStarC_SMap.try_find claimed tgt in
                          match uu___10 with
                          | FStar_Pervasives_Native.Some other ->
                              FStarC_Errors.raise_error0
                                FStarC_Errors_Codes.Error_CustardExportCollision
                                ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_list_doc)
                                (Obj.magic
                                   [FStarC_Errors_Msg.text
                                      (Prims.strcat
                                         "Custard: --custard_c_no_prefix would name both "
                                         (Prims.strcat other
                                            (Prims.strcat " and "
                                               (Prims.strcat src
                                                  (Prims.strcat " `"
                                                     (Prims.strcat tgt
                                                        "' in the generated C."))))));
                                   FStarC_Errors_Msg.text
                                     "Two definitions cannot share one external name."])
                          | FStar_Pervasives_Native.None -> ());
                         (let uu___11 = FStarC_SMap.try_find taken tgt in
                          match uu___11 with
                          | FStar_Pervasives_Native.Some other when
                              other <> src ->
                              FStarC_Errors.raise_error0
                                FStarC_Errors_Codes.Error_CustardExportCollision
                                ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_list_doc)
                                (Obj.magic
                                   [FStarC_Errors_Msg.text
                                      (Prims.strcat
                                         "Custard: --custard_c_no_prefix would name "
                                         (Prims.strcat src
                                            (Prims.strcat " `"
                                               (Prims.strcat tgt
                                                  (Prims.strcat
                                                     "', which is already the name of "
                                                     (Prims.strcat other "."))))));
                                   FStarC_Errors_Msg.text
                                     "Rename one of them, or drop the option for this module."])
                          | uu___12 -> ());
                         FStarC_SMap.add claimed tgt src;
                         (let uu___12 = FStarC_Effect.op_Bang renames in
                          FStarC_SMap.add uu___12 src tgt)))
                     else ()
                 | uu___6 -> ())) uu___3);
      FStarC_List.iter
        (fun m ->
           let uu___3 =
             let uu___4 = FStarC_SMap.try_find used_mod m in
             match uu___4 with
             | FStar_Pervasives_Native.None -> true
             | uu___5 -> false in
           if uu___3
           then
             FStarC_Errors.log_issue0
               FStarC_Errors_Codes.Warning_CustardNoPublicDefinitions ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic
                  [FStarC_Errors_Msg.text
                     (Prims.strcat "Custard: --custard_c_no_prefix "
                        (Prims.strcat m " renamed nothing."));
                  FStarC_Errors_Msg.text
                    "The option applies to types, to assume vals, and to definitions with external linkage.  Name the module with --custard_entry_module, or its definitions with --custard_entry, so that they are part of this unit's interface."])
           else ()) mods))
let build_macros (p : FStarC_Custard_Syntax.program) : unit=
  (let uu___1 = FStarC_SMap.create Prims.int_zero in
   FStarC_Effect.op_Colon_Equals macros uu___1);
  (let ms =
     FStarC_List.collect
       (fun d ->
          match d with
          | FStarC_Custard_Syntax.DLet l when is_macro l ->
              [l.FStarC_Custard_Syntax.dl_name]
          | uu___1 -> []) p in
   if (match ms with | [] -> true | uu___2 -> false)
   then ()
   else
     (let taken = FStarC_SMap.create (Prims.of_int 50) in
      FStarC_List.iter
        (fun d ->
           let n = FStarC_Custard_Syntax.name_of_decl d in
           let uu___3 =
             FStarC_List.existsb
               (fun m ->
                  let uu___4 = FStarC_Custard_Syntax.string_of_name m in
                  let uu___5 = FStarC_Custard_Syntax.string_of_name n in
                  uu___4 = uu___5) ms in
           if uu___3
           then ()
           else
             (let uu___4 = c_name n in
              let uu___5 = FStarC_Custard_Syntax.string_of_name n in
              FStarC_SMap.add taken uu___4 uu___5)) p;
      FStarC_List.iter
        (fun n ->
           let m = let uu___3 = c_name n in FStarC_String.uppercase uu___3 in
           let clash =
             let uu___3 = FStarC_SMap.try_find taken m in
             match uu___3 with
             | FStar_Pervasives_Native.Some o ->
                 FStar_Pervasives_Native.Some o
             | FStar_Pervasives_Native.None ->
                 let uu___4 = FStarC_Effect.op_Bang macros in
                 FStarC_SMap.try_find uu___4 m in
           match clash with
           | FStar_Pervasives_Native.Some o ->
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = FStarC_Custard_Syntax.string_of_name n in
                       Prims.strcat uu___7
                         (Prims.strcat " is "
                            (Prims.strcat m
                               (Prims.strcat
                                  ", which is already the C name of "
                                  (Prims.strcat o ".")))) in
                     Prims.strcat "Custard: the macro for " uu___6 in
                   FStarC_Errors_Msg.text uu___5 in
                 [uu___4;
                 FStarC_Errors_Msg.text
                   "A [@@ CMacro ] definition is spelled in upper case, following karamel, and the preprocessor rewrites that token everywhere in the translation unit -- including in the other declaration, which would then be unspellable.";
                 FStarC_Errors_Msg.text
                   "Rename one of the two, or drop the attribute."] in
               FStarC_Errors.raise_error0
                 FStarC_Errors_Codes.Error_CustardExportCollision ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___3)
           | FStar_Pervasives_Native.None ->
               ((let uu___4 = FStarC_Effect.op_Bang macros in
                 let uu___5 = FStarC_Custard_Syntax.string_of_name n in
                 FStarC_SMap.add uu___4 uu___5 m);
                (let uu___4 = FStarC_Effect.op_Bang macros in
                 let uu___5 = FStarC_Custard_Syntax.string_of_name n in
                 FStarC_SMap.add uu___4 m uu___5))) ms);
   (let final = FStarC_SMap.create (Prims.of_int 20) in
    FStarC_List.iter
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DLet l when is_macro l ->
             let uu___3 =
               let uu___4 = FStarC_Effect.op_Bang macros in
               let uu___5 =
                 FStarC_Custard_Syntax.string_of_name
                   l.FStarC_Custard_Syntax.dl_name in
               FStarC_SMap.try_find uu___4 uu___5 in
             (match uu___3 with
              | FStar_Pervasives_Native.Some m ->
                  let uu___4 =
                    FStarC_Custard_Syntax.string_of_name
                      l.FStarC_Custard_Syntax.dl_name in
                  FStarC_SMap.add final uu___4 m
              | FStar_Pervasives_Native.None -> ())
         | uu___3 -> ()) p;
    FStarC_Effect.op_Colon_Equals macros final))
let check_reference_copies (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun uu___ ->
       match uu___ with
       | FStarC_Custard_Syntax.DLet l ->
           FStarC_List.iter
             (fun b ->
                let uu___1 = binds_by_ref b.FStarC_Custard_Syntax.b_ty in
                if uu___1
                then
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            FStarC_Custard_Syntax.string_of_name
                              l.FStarC_Custard_Syntax.dl_name in
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    base_ty b.FStarC_Custard_Syntax.b_ty in
                                  Prims.strcat uu___11
                                    "', whose values are handles, and a parameter is a copy." in
                                Prims.strcat " at the type `" uu___10 in
                              Prims.strcat b.FStarC_Custard_Syntax.b_name
                                uu___9 in
                            Prims.strcat " takes " uu___8 in
                          Prims.strcat uu___6 uu___7 in
                        Prims.strcat "Custard: " uu___5 in
                      FStarC_Errors_Msg.text uu___4 in
                    [uu___3;
                    FStarC_Errors_Msg.text
                      "A write the callee makes through it is made to the copy and is lost when the call returns.  [@@custard_c_reference] binds a *local* by reference; it does not change a signature, because a reference parameter would then refuse every argument that is not an lvalue.";
                    FStarC_Errors_Msg.text
                      "If the callee only reads the argument this is fine.  If it writes, pass the container and the index instead, or make the callee external."] in
                  FStarC_Errors.log_issue0
                    FStarC_Errors_Codes.Warning_CustardReferenceCopied ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___2)
                else ()) l.FStarC_Custard_Syntax.dl_binders
       | uu___1 -> ()) p
let check_interface_names (p : FStarC_Custard_Syntax.program) : unit=
  let rec spec_names c =
    match c with
    | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
        let uu___1 = spec_names a in
        let uu___2 = spec_names b in FStarC_List.op_At uu___1 uu___2
    | FStarC_Custard_Syntax.TTuple cs -> FStarC_List.collect spec_names cs
    | FStarC_Custard_Syntax.TBuf c1 -> spec_names c1
    | FStarC_Custard_Syntax.TRef c1 -> spec_names c1
    | FStarC_Custard_Syntax.TInline c1 -> spec_names c1
    | FStarC_Custard_Syntax.TApp (n, args) ->
        let uu___ = FStarC_List.collect spec_names args in
        FStarC_List.op_At
          (if
             match n.FStarC_Custard_Syntax.spec with
             | FStar_Pervasives_Native.Some v -> true
             | uu___1 -> false
           then [n]
           else []) uu___
    | uu___ -> [] in
  let declared1 = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun uu___1 ->
       match uu___1 with
       | FStarC_Custard_Syntax.DType t ->
           let uu___2 =
             FStarC_Custard_Syntax.string_of_name
               t.FStarC_Custard_Syntax.dt_name in
           FStarC_SMap.add declared1 uu___2 true
       | uu___2 -> ()) p;
  (let aliases = FStarC_SMap.create (Prims.of_int 20) in
   FStarC_List.iter
     (fun uu___2 ->
        match uu___2 with
        | FStarC_Custard_Syntax.DType t ->
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TAbbrev (FStarC_Custard_Syntax.TApp
                 (n, [])) when
                 (match t.FStarC_Custard_Syntax.dt_params with
                  | [] -> true
                  | uu___3 -> false) &&
                   (match (t.FStarC_Custard_Syntax.dt_name).FStarC_Custard_Syntax.spec
                    with
                    | FStar_Pervasives_Native.None -> true
                    | uu___3 -> false)
                 ->
                 let uu___3 = FStarC_Custard_Syntax.string_of_name n in
                 let uu___4 = c_name t.FStarC_Custard_Syntax.dt_name in
                 FStarC_SMap.add aliases uu___3 uu___4
             | uu___3 -> ())
        | uu___3 -> ()) p;
   (let seen = FStarC_SMap.create (Prims.of_int 10) in
    FStarC_List.iter
      (fun uu___2 ->
         match uu___2 with
         | FStarC_Custard_Syntax.DLet l when is_public l ->
             let sig_ctys =
               let uu___3 =
                 FStarC_List.map (fun b -> b.FStarC_Custard_Syntax.b_ty)
                   l.FStarC_Custard_Syntax.dl_binders in
               FStarC_List.op_At uu___3 [l.FStarC_Custard_Syntax.dl_ret] in
             let uu___3 = FStarC_List.collect spec_names sig_ctys in
             FStarC_List.iter
               (fun n ->
                  let s = FStarC_Custard_Syntax.string_of_name n in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_SMap.try_find declared1 s in
                      match uu___6 with
                      | FStar_Pervasives_Native.Some v -> true
                      | uu___7 -> false in
                    if uu___5
                    then
                      let uu___6 = FStarC_SMap.try_find seen s in
                      match uu___6 with
                      | FStar_Pervasives_Native.None -> true
                      | uu___7 -> false
                    else false in
                  if uu___4
                  then
                    (FStarC_SMap.add seen s true;
                     (let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              let uu___10 = c_name n in
                              let uu___11 =
                                let uu___12 =
                                  let uu___13 =
                                    FStarC_Custard_Syntax.string_of_name
                                      l.FStarC_Custard_Syntax.dl_name in
                                  Prims.strcat uu___13
                                    " has it in its signature -- but its name is generated." in
                                Prims.strcat
                                  "' is part of this unit's interface -- "
                                  uu___12 in
                              Prims.strcat uu___10 uu___11 in
                            Prims.strcat "Custard: the type `" uu___9 in
                          FStarC_Errors_Msg.text uu___8 in
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 = FStarC_SMap.try_find aliases s in
                              match uu___11 with
                              | FStar_Pervasives_Native.Some alias ->
                                  FStarC_Errors_Msg.text
                                    (Prims.strcat
                                       "This header already publishes `"
                                       (Prims.strcat alias
                                          "' as another name for it; spell that instead."))
                              | FStar_Pervasives_Native.None ->
                                  FStarC_Errors_Msg.text
                                    "A consumer that must spell it should typedef it once, in its own header, rather than depend on this name throughout." in
                            [uu___10] in
                          (FStarC_Errors_Msg.text
                             "It is a specialization, so the name carries a hint built from the monomorphizer's input and may change when that input does. --custard_c_no_prefix does not rename specializations.")
                            :: uu___9 in
                        uu___7 :: uu___8 in
                      FStarC_Errors.log_issue0
                        FStarC_Errors_Codes.Warning_CustardGeneratedNameInInterface
                        ()
                        (Obj.magic
                           FStarC_Errors_Msg.is_error_message_list_doc)
                        (Obj.magic uu___6)))
                  else ()) uu___3
         | uu___3 -> ()) p))
let check_emitted_names (init_name1 : Prims.string)
  (p : FStarC_Custard_Syntax.program) : unit=
  let seen = FStarC_SMap.create (Prims.of_int 50) in
  let claim nm who ext =
    let uu___ = FStarC_SMap.try_find seen nm in
    match uu___ with
    | FStar_Pervasives_Native.Some (other, ext') when
        (other <> who) && (Prims.not (ext && ext')) ->
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Error_CustardExportCollision ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             (FStarC_List.op_At
                [FStarC_Errors_Msg.text
                   (Prims.strcat "Custard: "
                      (Prims.strcat other
                         (Prims.strcat " and "
                            (Prims.strcat who
                               (Prims.strcat " are both named `"
                                  (Prims.strcat nm "' in the generated C."))))));
                FStarC_Errors_Msg.text
                  "Two declarations cannot share one C name."]
                (if ext || ext'
                 then
                   [FStarC_Errors_Msg.text
                      "A name given by [@@custard_extern] is taken verbatim and names a symbol outside this program, so a definition that lands on it would take that symbol over -- with no diagnostic from the C compiler and no link error, because the definition simply wins."]
                 else [])))
    | uu___1 -> FStarC_SMap.add seen nm (who, ext) in
  (let uu___1 =
     let uu___2 = global_inits_of p in
     match uu___2 with | hd::tl -> true | uu___3 -> false in
   if uu___1 then claim init_name1 "the generated initializer" false else ());
  FStarC_List.iter
    (fun d ->
       let uu___1 = let uu___2 = local d in Prims.not uu___2 in
       if uu___1
       then ()
       else
         (let n = FStarC_Custard_Syntax.name_of_decl d in
          let uu___2 = emitted_name d in
          let uu___3 = FStarC_Custard_Syntax.string_of_name n in
          let uu___4 =
            let uu___5 = extern_target d in
            match uu___5 with
            | FStar_Pervasives_Native.Some v -> true
            | uu___6 -> false in
          claim uu___2 uu___3 uu___4)) p
let record_parents (p : FStarC_Custard_Syntax.program) : unit=
  let defs = FStarC_SMap.create (Prims.of_int 50) in
  let own = FStarC_SMap.create (Prims.of_int 50) in
  FStarC_List.iter
    (fun d ->
       (let uu___2 =
          FStarC_Custard_Syntax.string_of_name
            (FStarC_Custard_Syntax.name_of_decl d) in
        FStarC_SMap.add defs uu___2 d);
       (match d with
        | FStarC_Custard_Syntax.DType t ->
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TVariant cs ->
                 FStarC_List.iter
                   (fun uu___2 ->
                      match uu___2 with
                      | (cn, uu___3) ->
                          let uu___4 =
                            FStarC_Custard_Syntax.string_of_name cn in
                          let uu___5 =
                            FStarC_Custard_Syntax.string_of_name
                              t.FStarC_Custard_Syntax.dt_name in
                          FStarC_SMap.add own uu___4 uu___5) cs
             | uu___2 -> ())
        | uu___2 -> ())) p;
  (let resolve n =
     let uu___1 = FStarC_SMap.try_find own n in
     match uu___1 with
     | FStar_Pervasives_Native.Some o -> o
     | FStar_Pervasives_Native.None -> n in
   let seen = FStarC_SMap.create (Prims.of_int 50) in
   let rec bfs front =
     match front with
     | [] -> ()
     | uu___1 ->
         let next =
           FStarC_List.collect
             (fun n ->
                let uu___2 = FStarC_SMap.try_find defs n in
                match uu___2 with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some d ->
                    let uu___3 = FStarC_Custard_Simplify.decl_deps d in
                    FStarC_List.collect
                      (fun c ->
                         let c1 = resolve c in
                         let uu___4 =
                           if c1 = n
                           then true
                           else
                             (let uu___5 = FStarC_SMap.try_find seen c1 in
                              match uu___5 with
                              | FStar_Pervasives_Native.Some v -> true
                              | uu___6 -> false) in
                         if uu___4
                         then []
                         else
                           (FStarC_SMap.add seen c1 true;
                            FStarC_SMap.add parents c1 n;
                            [c1])) uu___3) front in
         bfs next in
   let rec ty_names t acc =
     match t with
     | FStarC_Custard_Syntax.TApp (n, args) ->
         let uu___1 =
           let uu___2 = FStarC_Custard_Syntax.string_of_name n in uu___2 ::
             acc in
         FStarC_List.fold_right ty_names args uu___1
     | FStarC_Custard_Syntax.TArrow (a, uu___1, b) ->
         let uu___2 = ty_names b acc in ty_names a uu___2
     | FStarC_Custard_Syntax.TBuf e -> ty_names e acc
     | FStarC_Custard_Syntax.TRef e -> ty_names e acc
     | FStarC_Custard_Syntax.TInline e -> ty_names e acc
     | FStarC_Custard_Syntax.TTuple ts ->
         FStarC_List.fold_right ty_names ts acc
     | uu___1 -> acc in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DExternal x ->
            let uu___2 = ty_names x.FStarC_Custard_Syntax.dx_ty [] in
            FStarC_List.iter
              (fun tn ->
                 let uu___3 =
                   let uu___4 = FStarC_SMap.try_find frozen_by tn in
                   match uu___4 with
                   | FStar_Pervasives_Native.None -> true
                   | uu___5 -> false in
                 if uu___3
                 then
                   ((let uu___5 =
                       FStarC_Custard_Syntax.string_of_name
                         x.FStarC_Custard_Syntax.dx_name in
                     FStarC_SMap.add frozen_by tn uu___5);
                    (match x.FStarC_Custard_Syntax.dx_target with
                     | FStar_Pervasives_Native.Some t ->
                         FStarC_SMap.add frozen_by_target tn t
                     | FStar_Pervasives_Native.None -> ()))
                 else ()) uu___2
        | uu___2 -> ()) p;
   (let roots =
      FStarC_List.collect
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
             let n =
               FStarC_Custard_Syntax.string_of_name
                 (FStarC_Custard_Syntax.name_of_decl d) in
             (FStarC_SMap.add seen n true;
              FStarC_SMap.add root_decls n true;
              [n])
           else []) p in
    bfs roots))
let print_program (base : Prims.string) (cu : unit_info)
  (p : FStarC_Custard_Syntax.program) : (Prims.string * Prims.string)=
  let init_name1 = init_name cu in
  reset_program_state ();
  record_parents p;
  build_renames cu.cu_no_prefix p;
  FStarC_List.iter
    (fun d ->
       let uu___4 = FStarC_Effect.op_Bang taken_names in
       let uu___5 = emitted_name d in FStarC_SMap.add uu___4 uu___5 true) p;
  (let uu___5 = FStarC_Effect.op_Bang taken_names in
   FStarC_SMap.add uu___5 init_name1 true);
  (let tt = FStarC_SMap.create (Prims.of_int 50) in
   let ct = FStarC_SMap.create (Prims.of_int 50) in
   let xt = FStarC_SMap.create (Prims.of_int 20) in
   let kt = FStarC_SMap.create (Prims.of_int 50) in
   let vt = FStarC_SMap.create (Prims.of_int 50) in
   let at = FStarC_SMap.create (Prims.of_int 50) in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DType t ->
            ((let uu___7 =
                FStarC_Custard_Syntax.string_of_name
                  t.FStarC_Custard_Syntax.dt_name in
              FStarC_SMap.add tt uu___7 t);
             FStarC_List.iter
               (fun f ->
                  match f with
                  | FStarC_Custard_Syntax.Existential (c, fld) ->
                      let uu___8 =
                        FStarC_Custard_Syntax.string_of_name
                          t.FStarC_Custard_Syntax.dt_name in
                      FStarC_SMap.add existentials uu___8 (c, fld)
                  | uu___8 -> ()) t.FStarC_Custard_Syntax.dt_flags;
             (match t.FStarC_Custard_Syntax.dt_body with
              | FStarC_Custard_Syntax.TVariant cs ->
                  FStarC_List.iter
                    (fun uu___8 ->
                       match uu___8 with
                       | (c, fs) ->
                           let uu___9 =
                             FStarC_Custard_Syntax.string_of_name c in
                           FStarC_SMap.add ct uu___9 (t, fs)) cs
              | uu___8 -> ()))
        | FStarC_Custard_Syntax.DExternal x ->
            ((let uu___7 =
                FStarC_Custard_Syntax.string_of_name
                  x.FStarC_Custard_Syntax.dx_name in
              let uu___8 =
                match x.FStarC_Custard_Syntax.dx_target with
                | FStar_Pervasives_Native.Some "" ->
                    emitted_name (FStarC_Custard_Syntax.DExternal x)
                | FStar_Pervasives_Native.None ->
                    emitted_name (FStarC_Custard_Syntax.DExternal x)
                | FStar_Pervasives_Native.Some t -> t in
              FStarC_SMap.add xt uu___7 uu___8);
             (let flags =
                let uu___7 = arg_ctys x.FStarC_Custard_Syntax.dx_ty in
                FStarC_List.map
                  (fun a ->
                     Prims.not
                       (match a with
                        | FStarC_Custard_Syntax.TUnit -> true
                        | uu___8 -> false)) uu___7 in
              (let uu___8 = FStarC_List.existsb (fun b -> Prims.not b) flags in
               if uu___8
               then
                 let uu___9 =
                   FStarC_Custard_Syntax.string_of_name
                     x.FStarC_Custard_Syntax.dx_name in
                 FStarC_SMap.add kt uu___9 flags
               else ());
              (let uu___9 =
                 if match flags with | hd::tl -> true | uu___10 -> false
                 then
                   let uu___10 = ret_cty x.FStarC_Custard_Syntax.dx_ty in
                   match uu___10 with
                   | FStarC_Custard_Syntax.TUnit -> true
                   | uu___11 -> false
                 else false in
               if uu___9
               then
                 let uu___10 =
                   FStarC_Custard_Syntax.string_of_name
                     x.FStarC_Custard_Syntax.dx_name in
                 FStarC_SMap.add vt uu___10 true
               else ());
              (let n =
                 let uu___9 = FStarC_List.filter (fun b -> b) flags in
                 FStarC_List.length uu___9 in
               if n > Prims.int_zero
               then
                 let uu___9 =
                   FStarC_Custard_Syntax.string_of_name
                     x.FStarC_Custard_Syntax.dx_name in
                 FStarC_SMap.add at uu___9 n
               else ())))
        | FStarC_Custard_Syntax.DLet l ->
            let flags =
              FStarC_List.map
                (fun b ->
                   Prims.not
                     (match b.FStarC_Custard_Syntax.b_ty with
                      | FStarC_Custard_Syntax.TUnit -> true
                      | uu___6 -> false)) l.FStarC_Custard_Syntax.dl_binders in
            ((let uu___7 = FStarC_List.existsb (fun b -> Prims.not b) flags in
              if uu___7
              then
                let uu___8 =
                  FStarC_Custard_Syntax.string_of_name
                    l.FStarC_Custard_Syntax.dl_name in
                FStarC_SMap.add kt uu___8 flags
              else ());
             if
               (match l.FStarC_Custard_Syntax.dl_ret with
                | FStarC_Custard_Syntax.TUnit -> true
                | uu___8 -> false) &&
                 ((match l.FStarC_Custard_Syntax.dl_binders with
                   | hd::tl -> true
                   | uu___8 -> false))
             then
               (let uu___8 =
                  FStarC_Custard_Syntax.string_of_name
                    l.FStarC_Custard_Syntax.dl_name in
                FStarC_SMap.add vt uu___8 true)
             else ();
             (let n =
                let uu___8 = FStarC_List.filter (fun b -> b) flags in
                FStarC_List.length uu___8 in
              let uu___8 =
                FStarC_Custard_Syntax.string_of_name
                  l.FStarC_Custard_Syntax.dl_name in
              let uu___9 =
                if
                  match l.FStarC_Custard_Syntax.dl_binders with
                  | hd::tl -> true
                  | uu___10 -> false
                then n
                else
                  (let uu___10 =
                     let uu___11 = arg_ctys l.FStarC_Custard_Syntax.dl_ret in
                     FStarC_List.filter
                       (fun a ->
                          Prims.not
                            (match a with
                             | FStarC_Custard_Syntax.TUnit -> true
                             | uu___12 -> false)) uu___11 in
                   FStarC_List.length uu___10) in
              FStarC_SMap.add at uu___8 uu___9))
        | uu___6 -> ()) p;
   FStarC_Effect.op_Colon_Equals types tt;
   FStarC_Effect.op_Colon_Equals ctors ct;
   FStarC_Effect.op_Colon_Equals externs xt;
   FStarC_Effect.op_Colon_Equals keeps kt;
   FStarC_Effect.op_Colon_Equals void_fns vt;
   build_macros p;
   check_interface_names p;
   check_emitted_names init_name1 p;
   check_reference_copies p;
   FStarC_Effect.op_Colon_Equals arities at;
   (let banner = "/* Generated by F* Custard extraction. Do not edit. */\n" in
    let guard =
      let uu___16 =
        let uu___17 =
          let uu___18 = sanitize base in FStarC_String.uppercase uu___18 in
        Prims.strcat uu___17 "_H" in
      Prims.strcat "__" uu___16 in
    let header =
      Prims.strcat banner
        (Prims.strcat "#ifndef "
           (Prims.strcat guard
              (Prims.strcat "\n#define "
                 (Prims.strcat guard
                    "\n\n#include <stdint.h>\n#include <stdlib.h>\n#include <stdbool.h>\n#include <string.h>\n")))) in
    let includes =
      let uu___16 =
        FStarC_List.map
          (fun h -> Prims.strcat "#include \"" (Prims.strcat h "\""))
          cu.cu_headers in
      let uu___17 =
        FStarC_List.collect
          (fun d ->
             match d with
             | FStarC_Custard_Syntax.DExternal
                 { FStarC_Custard_Syntax.dx_name = uu___18;
                   FStarC_Custard_Syntax.dx_typars = uu___19;
                   FStarC_Custard_Syntax.dx_ty = uu___20;
                   FStarC_Custard_Syntax.dx_target = uu___21;
                   FStarC_Custard_Syntax.dx_header =
                     FStar_Pervasives_Native.Some h;
                   FStarC_Custard_Syntax.dx_flags = uu___22;_}
                 -> [Prims.strcat "#include \"" (Prims.strcat h "\"")]
             | FStarC_Custard_Syntax.DType ty1 ->
                 FStarC_List.collect
                   (fun f ->
                      match f with
                      | FStarC_Custard_Syntax.Extern
                          (uu___18, FStar_Pervasives_Native.Some h) ->
                          [Prims.strcat "#include \"" (Prims.strcat h "\"")]
                      | uu___18 -> []) ty1.FStarC_Custard_Syntax.dt_flags
             | uu___18 -> []) p in
      FStarC_List.op_At uu___16 uu___17 in
    let includes1 = dedup includes in
    let exts_named =
      FStarC_List.collect
        (fun d ->
           let uu___16 = let uu___17 = local d in Prims.not uu___17 in
           if uu___16
           then []
           else
             (match d with
              | FStarC_Custard_Syntax.DExternal x ->
                  let uu___17 = extern_decl x in
                  (match uu___17 with
                   | FStar_Pervasives_Native.Some s ->
                       let nm =
                         emitted_name (FStarC_Custard_Syntax.DExternal x) in
                       let uu___18 =
                         let uu___19 =
                           FStarC_Custard_Syntax.string_of_name
                             x.FStarC_Custard_Syntax.dx_name in
                         (nm, uu___19, s) in
                       [uu___18]
                   | FStar_Pervasives_Native.None -> [])
              | FStarC_Custard_Syntax.DExn uu___17 ->
                  (FStarC_Effect.op_Colon_Equals current
                     "an exception declaration";
                   reject "an exception declaration" ["C has no exceptions."])
              | uu___17 -> [])) p in
    (let seen = FStarC_SMap.create (Prims.of_int 20) in
     FStarC_List.iter
       (fun uu___17 ->
          match uu___17 with
          | (nm, src, s) ->
              let uu___18 = FStarC_SMap.try_find seen nm in
              (match uu___18 with
               | FStar_Pervasives_Native.Some (src', s') when s' <> s ->
                   let uu___19 =
                     let uu___20 =
                       let uu___21 =
                         let uu___22 =
                           let uu___23 =
                             let uu___24 =
                               let uu___25 = trim_nl s' in
                               Prims.strcat "' declares it as: " uu___25 in
                             Prims.strcat src' uu___24 in
                           Prims.strcat "'" uu___23 in
                         FStarC_Errors_Msg.text uu___22 in
                       let uu___22 =
                         let uu___23 =
                           let uu___24 =
                             let uu___25 =
                               let uu___26 =
                                 let uu___27 = trim_nl s in
                                 Prims.strcat "' declares it as: " uu___27 in
                               Prims.strcat src uu___26 in
                             Prims.strcat "'" uu___25 in
                           FStarC_Errors_Msg.text uu___24 in
                         [uu___23;
                         FStarC_Errors_Msg.text
                           "One C symbol has one prototype, so these cannot both be emitted.";
                         FStarC_Errors_Msg.text
                           "If the target really does accept both -- a variadic macro, or an overload set -- add [@@custard_c_header \"...\"] naming the header that declares it.  Custard then emits no prototype of its own and includes the header instead, which is the only arrangement in which several type vectors can share one symbol.";
                         FStarC_Errors_Msg.text
                           "Otherwise give each type vector its own [@@custard_extern] target name."] in
                       uu___21 :: uu___22 in
                     (FStarC_Errors_Msg.text
                        (Prims.strcat "Custard: the external target `"
                           (Prims.strcat nm
                              "' is declared twice, with different types.")))
                       :: uu___20 in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Error_CustardExternConflict ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___19)
               | uu___19 -> FStarC_SMap.add seen nm (src, s))) exts_named);
    (match () with
     | () ->
         let exts =
           let uu___17 =
             FStarC_List.map
               (fun uu___18 ->
                  match uu___18 with | (uu___19, uu___20, s) -> s) exts_named in
           dedup uu___17 in
         let fwds =
           FStarC_List.collect
             (fun d ->
                let uu___17 = let uu___18 = local d in Prims.not uu___18 in
                if uu___17
                then []
                else
                  (match d with
                   | FStarC_Custard_Syntax.DType t ->
                       ((let uu___19 =
                           FStarC_Custard_Syntax.string_of_name
                             t.FStarC_Custard_Syntax.dt_name in
                         FStarC_Effect.op_Colon_Equals current uu___19);
                        (let uu___19 = type_fwd t in
                         match uu___19 with
                         | FStar_Pervasives_Native.Some s -> [s]
                         | FStar_Pervasives_Native.None -> []))
                   | uu___18 -> [])) p in
         let tys =
           let uu___17 =
             let uu___18 =
               FStarC_List.collect
                 (fun d ->
                    match d with
                    | FStarC_Custard_Syntax.DType t when local d -> [t]
                    | uu___19 -> []) p in
             sort_types uu___18 in
           FStarC_List.collect
             (fun t ->
                (let uu___19 =
                   FStarC_Custard_Syntax.string_of_name
                     t.FStarC_Custard_Syntax.dt_name in
                 FStarC_Effect.op_Colon_Equals current uu___19);
                (let uu___19 = type_decl t in
                 match uu___19 with
                 | FStar_Pervasives_Native.Some s -> [s]
                 | FStar_Pervasives_Native.None -> [])) uu___17 in
         let proto_of l =
           (let uu___18 =
              FStarC_Custard_Syntax.string_of_name
                l.FStarC_Custard_Syntax.dl_name in
            FStarC_Effect.op_Colon_Equals current uu___18);
           reset_scope ();
           (let uu___20 = kept_binders l in
            FStarC_List.iter
              (fun b ->
                 let uu___21 = bind_var b.FStarC_Custard_Syntax.b_name in ())
              uu___20);
           (let uu___20 = signature l in Prims.strcat uu___20 ";\n") in
         let protos =
           FStarC_List.collect
             (fun d ->
                let uu___17 = let uu___18 = local d in Prims.not uu___18 in
                if uu___17
                then []
                else
                  (match d with
                   | FStarC_Custard_Syntax.DLet l when is_macro l ->
                       let uu___18 = is_public l in
                       if uu___18
                       then []
                       else
                         (let uu___19 =
                            let uu___20 = prologue_of l in
                            let uu___21 = macro_decl l in
                            Prims.strcat uu___20 uu___21 in
                          [uu___19])
                   | FStarC_Custard_Syntax.DLet l when
                       match l.FStarC_Custard_Syntax.dl_binders with
                       | [] -> true
                       | uu___18 -> false ->
                       let uu___18 =
                         let uu___19 = prologue_of l in
                         let uu___20 =
                           let uu___21 = storage l in
                           let uu___22 = global_decl l in
                           Prims.strcat uu___21 uu___22 in
                         Prims.strcat uu___19 uu___20 in
                       [uu___18]
                   | FStarC_Custard_Syntax.DLet l when
                       match l.FStarC_Custard_Syntax.dl_binders with
                       | hd::tl -> true
                       | uu___18 -> false ->
                       let uu___18 = is_public l in
                       if uu___18
                       then []
                       else
                         (let uu___19 =
                            let uu___20 = prologue_of l in
                            let uu___21 =
                              let uu___22 = storage l in
                              let uu___23 =
                                let uu___24 = inline_of l in
                                let uu___25 = proto_of l in
                                Prims.strcat uu___24 uu___25 in
                              Prims.strcat uu___22 uu___23 in
                            Prims.strcat uu___20 uu___21 in
                          [uu___19])
                   | uu___18 -> [])) p in
         let pub_decls =
           FStarC_List.collect
             (fun d ->
                let uu___17 = let uu___18 = local d in Prims.not uu___18 in
                if uu___17
                then []
                else
                  (match d with
                   | FStarC_Custard_Syntax.DLet l when
                       let uu___18 = is_public l in
                       if uu___18 then is_macro l else false ->
                       let uu___18 =
                         let uu___19 = prologue_of l in
                         let uu___20 = macro_decl l in
                         Prims.strcat uu___19 uu___20 in
                       [uu___18]
                   | FStarC_Custard_Syntax.DLet l when
                       let uu___18 = is_public l in
                       if uu___18
                       then
                         match l.FStarC_Custard_Syntax.dl_binders with
                         | [] -> true
                         | uu___19 -> false
                       else false ->
                       ((let uu___19 =
                           FStarC_Custard_Syntax.string_of_name
                             l.FStarC_Custard_Syntax.dl_name in
                         FStarC_Effect.op_Colon_Equals current uu___19);
                        (let uu___19 = array_extern l in
                         match uu___19 with
                         | FStar_Pervasives_Native.Some d1 ->
                             let uu___20 =
                               let uu___21 = prologue_of l in
                               Prims.strcat uu___21 d1 in
                             [uu___20]
                         | FStar_Pervasives_Native.None ->
                             let uu___20 =
                               let uu___21 = prologue_of l in
                               let uu___22 =
                                 let uu___23 =
                                   let uu___24 =
                                     let uu___25 =
                                       c_name l.FStarC_Custard_Syntax.dl_name in
                                     decl_of l.FStarC_Custard_Syntax.dl_ret
                                       uu___25 in
                                   Prims.strcat uu___24 ";\n" in
                                 Prims.strcat "extern " uu___23 in
                               Prims.strcat uu___21 uu___22 in
                             [uu___20]))
                   | FStarC_Custard_Syntax.DLet l when is_public l ->
                       let uu___18 =
                         let uu___19 = prologue_of l in
                         let uu___20 =
                           let uu___21 = inline_of l in
                           let uu___22 = proto_of l in
                           Prims.strcat uu___21 uu___22 in
                         Prims.strcat uu___19 uu___20 in
                       [uu___18]
                   | uu___18 -> [])) p in
         let defs =
           FStarC_List.collect
             (fun d ->
                let uu___17 = let uu___18 = local d in Prims.not uu___18 in
                if uu___17
                then []
                else
                  (match d with
                   | FStarC_Custard_Syntax.DLet l when
                       match l.FStarC_Custard_Syntax.dl_binders with
                       | [] -> true
                       | uu___18 -> false -> []
                   | FStarC_Custard_Syntax.DLet l ->
                       let uu___18 =
                         let uu___19 = comment_of l in
                         let uu___20 =
                           let uu___21 = prologue_of l in
                           let uu___22 =
                             let uu___23 = storage l in
                             let uu___24 =
                               let uu___25 = inline_of l in
                               let uu___26 =
                                 let uu___27 = let_decl l in
                                 let uu___28 = epilogue_of l in
                                 Prims.strcat uu___27 uu___28 in
                               Prims.strcat uu___25 uu___26 in
                             Prims.strcat uu___23 uu___24 in
                           Prims.strcat uu___21 uu___22 in
                         Prims.strcat uu___19 uu___20 in
                       [uu___18]
                   | uu___18 -> [])) p in
         let inits =
           let uu___17 = global_inits_of p in
           FStarC_List.map global_init uu___17 in
         let init_guard =
           match cu.cu_name with
           | FStar_Pervasives_Native.None -> ""
           | FStar_Pervasives_Native.Some uu___17 ->
               "  static bool custard_initialized = false;\n  if (custard_initialized) return;\n  custard_initialized = true;\n" in
         let init_fn =
           match inits with
           | [] -> ""
           | uu___17 ->
               Prims.strcat "void "
                 (Prims.strcat init_name1
                    (Prims.strcat "(void) {\n"
                       (Prims.strcat init_guard
                          (Prims.strcat (FStarC_String.concat "" inits) "}\n")))) in
         let init_proto =
           match inits with
           | [] -> ""
           | uu___17 ->
               Prims.strcat "void " (Prims.strcat init_name1 "(void);\n") in
         let mains =
           FStarC_List.collect
             (fun d ->
                let uu___17 = let uu___18 = local d in Prims.not uu___18 in
                if uu___17
                then []
                else
                  (match d with
                   | FStarC_Custard_Syntax.DLet l when
                       FStarC_List.existsb
                         FStarC_Custard_Syntax.uu___is_Entrypoint
                         l.FStarC_Custard_Syntax.dl_flags
                       ->
                       ((let uu___19 =
                           FStarC_Custard_Syntax.string_of_name
                             l.FStarC_Custard_Syntax.dl_name in
                         FStarC_Effect.op_Colon_Equals current uu___19);
                        (let args =
                           let uu___19 =
                             let uu___20 = kept_binders l in
                             FStarC_List.map (fun uu___21 -> unit_value)
                               uu___20 in
                           FStarC_String.concat ", " uu___19 in
                         let call =
                           let uu___19 =
                             c_name l.FStarC_Custard_Syntax.dl_name in
                           Prims.strcat uu___19
                             (Prims.strcat "(" (Prims.strcat args ")")) in
                         let calls =
                           let uu___19 =
                             FStarC_List.map
                               (fun i ->
                                  Prims.strcat "  " (Prims.strcat i "();\n"))
                               cu.cu_inits in
                           FStarC_List.op_At uu___19
                             (match inits with
                              | [] -> []
                              | uu___20 ->
                                  [Prims.strcat "  "
                                     (Prims.strcat init_name1 "();\n")]) in
                         let pre =
                           Prims.strcat "int main(void) {\n"
                             (FStarC_String.concat "" calls) in
                         match l.FStarC_Custard_Syntax.dl_ret with
                         | FStarC_Custard_Syntax.TInt uu___19 ->
                             [Prims.strcat pre
                                (Prims.strcat "  return (int)"
                                   (Prims.strcat call ";\n}\n"))]
                         | FStarC_Custard_Syntax.TUnit ->
                             [Prims.strcat pre
                                (Prims.strcat "  "
                                   (Prims.strcat call ";\n  return 0;\n}\n"))]
                         | uu___19 ->
                             [Prims.strcat pre
                                (Prims.strcat "  (void)"
                                   (Prims.strcat call ";\n  return 0;\n}\n"))]))
                   | uu___18 -> [])) p in
         let uu___17 = eq_decls () in
         (match uu___17 with
          | (eq_protos, eq_defs) ->
              let cpp_open = "#ifdef __cplusplus\nextern \"C\" {\n#endif\n\n" in
              let cpp_close = "\n#ifdef __cplusplus\n}\n#endif\n" in
              let hdr_body =
                Prims.strcat cpp_open
                  (Prims.strcat (FStarC_String.concat "" fwds)
                     (Prims.strcat
                        (match fwds with | [] -> "" | uu___18 -> "\n")
                        (Prims.strcat (FStarC_String.concat "" tys)
                           (Prims.strcat
                              (match tys with | [] -> "" | uu___18 -> "\n")
                              (Prims.strcat
                                 (FStarC_String.concat "" pub_decls)
                                 (Prims.strcat
                                    (match pub_decls with
                                     | [] -> ""
                                     | uu___18 -> "\n")
                                    (Prims.strcat init_proto
                                       (Prims.strcat
                                          (match inits with
                                           | [] -> ""
                                           | uu___18 -> "\n") cpp_close)))))))) in
              let src_body =
                Prims.strcat (FStarC_String.concat "" exts)
                  (Prims.strcat
                     (match exts with | [] -> "" | uu___18 -> "\n")
                     (Prims.strcat (FStarC_String.concat "" protos)
                        (Prims.strcat
                           (match protos with | [] -> "" | uu___18 -> "\n")
                           (Prims.strcat (FStarC_String.concat "" eq_protos)
                              (Prims.strcat
                                 (match eq_protos with
                                  | [] -> ""
                                  | uu___18 -> "\n")
                                 (Prims.strcat
                                    (FStarC_String.concat "\n" eq_defs)
                                    (Prims.strcat
                                       (match eq_defs with
                                        | [] -> ""
                                        | uu___18 -> "\n")
                                       (Prims.strcat
                                          (FStarC_String.concat "\n" defs)
                                          (Prims.strcat "\n"
                                             (Prims.strcat
                                                (match inits with
                                                 | [] -> ""
                                                 | uu___18 -> init_fn)
                                                (match mains with
                                                 | [] -> ""
                                                 | uu___18 ->
                                                     Prims.strcat "\n"
                                                       (FStarC_String.concat
                                                          "\n" mains)))))))))))) in
              let hdr_narrow = mentions_narrow hdr_body in
              let hdr_unit = mentions_unit hdr_body in
              let hdr_fspec = mentions_float_special hdr_body in
              let hdr =
                Prims.strcat header
                  (Prims.strcat
                     (match includes1 with
                      | [] -> ""
                      | uu___18 ->
                          Prims.strcat "\n"
                            (Prims.strcat
                               (FStarC_String.concat "\n" includes1) "\n"))
                     (Prims.strcat
                        (if hdr_unit
                         then Prims.strcat "\n" unit_support
                         else "")
                        (Prims.strcat
                           (if hdr_fspec
                            then Prims.strcat "\n" float_special_support
                            else "")
                           (Prims.strcat
                              (if hdr_narrow then narrow_support else "")
                              (Prims.strcat "\n"
                                 (Prims.strcat hdr_body "#endif\n")))))) in
              let body =
                Prims.strcat banner
                  (Prims.strcat "#include \""
                     (Prims.strcat base
                        (Prims.strcat ".h\"\n"
                           (Prims.strcat
                              (if
                                 (Prims.not hdr_unit) &&
                                   (mentions_unit src_body)
                               then Prims.strcat "\n" unit_support
                               else "")
                              (Prims.strcat
                                 (if
                                    (Prims.not hdr_fspec) &&
                                      (mentions_float_special src_body)
                                  then
                                    Prims.strcat "\n" float_special_support
                                  else "")
                                 (Prims.strcat
                                    (if
                                       (Prims.not hdr_narrow) &&
                                         (mentions_narrow src_body)
                                     then narrow_support
                                     else "") (Prims.strcat "\n" src_body))))))) in
              (hdr, body)))))
