open Prims
let current_module :
  Prims.string FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let externals : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let unqualify_self (t : Prims.string) : Prims.string=
  let uu___ = FStarC_Effect.op_Bang current_module in
  match uu___ with
  | FStar_Pervasives_Native.None -> t
  | FStar_Pervasives_Native.Some m ->
      let p = Prims.strcat m "." in
      let lp = FStarC_String.strlen p in
      let uu___1 =
        if (FStarC_String.strlen t) > lp
        then
          let uu___2 = FStarC_String.substring t Prims.int_zero lp in
          uu___2 = p
        else false in
      if uu___1
      then FStarC_String.substring t lp ((FStarC_String.strlen t) - lp)
      else t
let external_target (n : FStarC_Custard_Syntax.name) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang externals in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | FStar_Pervasives_Native.Some t ->
      let uu___1 = unqualify_self t in FStar_Pervasives_Native.Some uu___1
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let qualifiers : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let realized : unit FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let is_realized (n : FStarC_Custard_Syntax.name) : Prims.bool=
  if
    match n.FStarC_Custard_Syntax.spec with
    | FStar_Pervasives_Native.None -> true
    | uu___ -> false
  then
    let uu___ =
      let uu___1 = FStarC_Effect.op_Bang realized in
      let uu___2 = FStarC_Custard_Syntax.string_of_name n in
      FStarC_SMap.try_find uu___1 uu___2 in
    match uu___ with
    | FStar_Pervasives_Native.Some v -> true
    | uu___1 -> false
  else false
let at_home : unit FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let is_at_home (n : FStarC_Custard_Syntax.name) : Prims.bool=
  if
    match n.FStarC_Custard_Syntax.spec with
    | FStar_Pervasives_Native.None -> true
    | uu___ -> false
  then
    let uu___ =
      let uu___1 = FStarC_Effect.op_Bang at_home in
      let uu___2 = FStarC_Custard_Syntax.string_of_name n in
      FStarC_SMap.try_find uu___1 uu___2 in
    match uu___ with
    | FStar_Pervasives_Native.Some v -> true
    | uu___1 -> false
  else false
let exn_idents : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let tuples : Prims.int FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let record_params : Prims.int FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let record_labels : Prims.int FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let label_key (n : FStarC_Custard_Syntax.name) (f : Prims.string) :
  Prims.string=
  Prims.strcat (FStarC_String.concat "." n.FStarC_Custard_Syntax.ns)
    (Prims.strcat "|" f)
let ambiguous_label (n : FStarC_Custard_Syntax.name) (f : Prims.string) :
  Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang record_labels in
    FStarC_SMap.try_find uu___1 (label_key n f) in
  match uu___ with
  | FStar_Pervasives_Native.Some k -> k > Prims.int_one
  | FStar_Pervasives_Native.None -> false
let is_tuple_type (n : FStarC_Custard_Syntax.name) : Prims.bool=
  ((match n.FStarC_Custard_Syntax.spec with
    | FStar_Pervasives_Native.None -> true
    | uu___ -> false) &&
     (n.FStarC_Custard_Syntax.ns = ["FStar"; "Pervasives"; "Native"]))
    && (FStarC_Util.starts_with n.FStarC_Custard_Syntax.id "tuple")
let tuple_arity (n : FStarC_Custard_Syntax.name) :
  Prims.int FStar_Pervasives_Native.option=
  if
    match n.FStarC_Custard_Syntax.spec with
    | FStar_Pervasives_Native.Some v -> true
    | uu___ -> false
  then FStar_Pervasives_Native.None
  else
    (let uu___ = FStarC_Effect.op_Bang tuples in
     let uu___1 = FStarC_Custard_Syntax.string_of_name n in
     FStarC_SMap.try_find uu___ uu___1)
let tuple_index (f : Prims.string) : Prims.int=
  let s =
    let uu___ =
      if (FStarC_String.strlen f) > Prims.int_zero
      then
        let uu___1 = FStarC_String.substring f Prims.int_zero Prims.int_one in
        uu___1 = "_"
      else false in
    if uu___
    then
      FStarC_String.substring f Prims.int_one
        ((FStarC_String.strlen f) - Prims.int_one)
    else f in
  match FStarC_Util.safe_int_of_string s with
  | FStar_Pervasives_Native.Some i -> i
  | FStar_Pervasives_Native.None -> Prims.int_zero
let by_position (k : Prims.int) (dflt : Prims.string)
  (fs : (Prims.string * Prims.string) Prims.list) : Prims.string Prims.list=
  let at i =
    let uu___ =
      FStarC_List.tryPick
        (fun uu___1 ->
           match uu___1 with
           | (f, s) ->
               let uu___2 = let uu___3 = tuple_index f in uu___3 = i in
               if uu___2
               then FStar_Pervasives_Native.Some s
               else FStar_Pervasives_Native.None) fs in
    match uu___ with
    | FStar_Pervasives_Native.Some s -> s
    | FStar_Pervasives_Native.None -> dflt in
  let rec go i =
    if i > k
    then []
    else
      (let uu___ = at i in
       let uu___1 = go (i + Prims.int_one) in uu___ :: uu___1) in
  go Prims.int_one
let qualifier (n : FStarC_Custard_Syntax.name) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang qualifiers in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | FStar_Pervasives_Native.Some m ->
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang current_module in
        (FStar_Pervasives_Native.Some m) = uu___2 in
      if uu___1
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some m
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let qualify (n : FStarC_Custard_Syntax.name) (s : Prims.string) :
  Prims.string=
  let uu___ = qualifier n in
  match uu___ with
  | FStar_Pervasives_Native.Some m -> Prims.strcat m (Prims.strcat "." s)
  | FStar_Pervasives_Native.None -> s
let ocaml_keywords : Prims.string Prims.list=
  ["and";
  "as";
  "assert";
  "begin";
  "class";
  "constraint";
  "do";
  "done";
  "downto";
  "else";
  "end";
  "exception";
  "external";
  "false";
  "for";
  "fun";
  "function";
  "functor";
  "if";
  "in";
  "include";
  "inherit";
  "initializer";
  "lazy";
  "let";
  "match";
  "method";
  "module";
  "mutable";
  "new";
  "nonrec";
  "object";
  "of";
  "open";
  "or";
  "private";
  "rec";
  "sig";
  "struct";
  "then";
  "to";
  "true";
  "try";
  "type";
  "val";
  "virtual";
  "when";
  "while";
  "with";
  "asr";
  "land";
  "lor";
  "lsl";
  "lsr";
  "lxor";
  "mod"]
let is_alpha (i : Prims.int) : Prims.bool=
  ((i >= (Prims.of_int 97)) && (i <= (Prims.of_int 122))) ||
    ((i >= (Prims.of_int 65)) && (i <= (Prims.of_int 90)))
let sanitize (s : Prims.string) : Prims.string=
  let ok c =
    let i = FStarC_Util.int_of_char c in
    (((is_alpha i) || ((i >= (Prims.of_int 48)) && (i <= (Prims.of_int 57))))
       || (i = (Prims.of_int 95)))
      || (i = (Prims.of_int 39)) in
  let uu___ =
    FStarC_List.map
      (fun c ->
         let uu___1 = ok c in
         if uu___1 then FStarC_Util.string_of_char c else "_")
      (FStarC_String.list_of_string s) in
  FStarC_String.concat "" uu___
let lowercase_first (s : Prims.string) : Prims.string=
  if s = ""
  then "x"
  else
    (let i =
       FStarC_Util.int_of_char
         (FStarC_List.hd (FStarC_String.list_of_string s)) in
     let tl =
       FStarC_String.substring s Prims.int_one
         ((FStarC_String.length s) - Prims.int_one) in
     if (i >= (Prims.of_int 65)) && (i <= (Prims.of_int 90))
     then
       let uu___ =
         let uu___1 = FStarC_String.substring s Prims.int_zero Prims.int_one in
         FStarC_String.lowercase uu___1 in
       Prims.strcat uu___ tl
     else
       if (i >= (Prims.of_int 97)) && (i <= (Prims.of_int 122))
       then s
       else Prims.strcat "u_" s)
let uppercase_first (s : Prims.string) : Prims.string=
  if s = ""
  then "X"
  else
    (let i =
       FStarC_Util.int_of_char
         (FStarC_List.hd (FStarC_String.list_of_string s)) in
     let hd =
       let uu___ = FStarC_String.substring s Prims.int_zero Prims.int_one in
       FStarC_String.uppercase uu___ in
     let tl =
       FStarC_String.substring s Prims.int_one
         ((FStarC_String.length s) - Prims.int_one) in
     if is_alpha i then Prims.strcat hd tl else Prims.strcat "U" s)
let escape_keyword (s : Prims.string) : Prims.string=
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
      ocaml_keywords in
  if uu___ then Prims.strcat s "_" else s
let ocaml_value_name (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ = is_at_home n in
  if uu___
  then
    let uu___1 =
      let uu___2 = sanitize n.FStarC_Custard_Syntax.id in
      lowercase_first uu___2 in
    escape_keyword uu___1
  else
    (let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_Custard_Syntax.mangled_name n in sanitize uu___3 in
       lowercase_first uu___2 in
     escape_keyword uu___1)
let ocaml_type_name (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ = is_realized n in
  if uu___
  then sanitize n.FStarC_Custard_Syntax.id
  else
    (let uu___1 = is_at_home n in
     if uu___1
     then
       let uu___2 =
         let uu___3 = sanitize n.FStarC_Custard_Syntax.id in
         lowercase_first uu___3 in
       escape_keyword uu___2
     else
       (let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Custard_Syntax.mangled_name n in
            sanitize uu___4 in
          lowercase_first uu___3 in
        escape_keyword uu___2))
let ocaml_ctor_ident (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ =
    let uu___1 = is_realized n in if uu___1 then true else is_at_home n in
  if uu___
  then
    let uu___1 = sanitize n.FStarC_Custard_Syntax.id in
    uppercase_first uu___1
  else
    (let uu___1 =
       let uu___2 = FStarC_Effect.op_Bang exn_idents in
       let uu___3 = FStarC_Custard_Syntax.string_of_name n in
       FStarC_SMap.try_find uu___2 uu___3 in
     match uu___1 with
     | FStar_Pervasives_Native.Some s -> s
     | FStar_Pervasives_Native.None ->
         let uu___2 =
           let uu___3 = FStarC_Custard_Syntax.mangled_name n in
           sanitize uu___3 in
         uppercase_first uu___2)
let predefined_ctors : Prims.string Prims.list=
  ["Out_of_memory";
  "Sys_error";
  "Failure";
  "Invalid_argument";
  "End_of_file";
  "Division_by_zero";
  "Not_found";
  "Match_failure";
  "Stack_overflow";
  "Sys_blocked_io";
  "Assert_failure";
  "Undefined_recursive_module";
  "Exit";
  "None";
  "Some";
  "Nil";
  "Cons"]
let ocaml_ctor_name (n : FStarC_Custard_Syntax.name) (c : Prims.string) :
  Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Custard_Syntax.mangled_name n in
      Prims.strcat uu___2 (Prims.strcat "_" c) in
    sanitize uu___1 in
  uppercase_first uu___
let module_name_of_unit (u : Prims.string) : Prims.string=
  let uu___ = sanitize u in uppercase_first uu___
let ocaml_var (x : Prims.string) : Prims.string=
  let uu___ = let uu___1 = sanitize x in lowercase_first uu___1 in
  escape_keyword uu___
let reserved_top : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let ocaml_local (x : Prims.string) : Prims.string=
  let s = ocaml_var x in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang reserved_top in
    FStarC_List.existsb (fun k -> k = s) uu___1 in
  if uu___ then Prims.strcat s "_" else s
let realization_of (n : FStarC_Custard_Syntax.name) : Prims.string=
  match n.FStarC_Custard_Syntax.ns with
  | [] ->
      let uu___ = sanitize n.FStarC_Custard_Syntax.id in
      lowercase_first uu___
  | ns ->
      let uu___ =
        let uu___1 =
          let uu___2 = sanitize n.FStarC_Custard_Syntax.id in
          lowercase_first uu___2 in
        Prims.strcat "." uu___1 in
      Prims.strcat (FStarC_String.concat "_" ns) uu___
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
  | "Prims.unit" -> FStar_Pervasives_Native.Some "unit"
  | "Prims.bool" -> FStar_Pervasives_Native.Some "bool"
  | "Prims.string" -> FStar_Pervasives_Native.Some "string"
  | "Prims.int" -> FStar_Pervasives_Native.Some "Prims.int"
  | "Prims.exn" -> FStar_Pervasives_Native.Some "exn"
  | "Prims.list" -> FStar_Pervasives_Native.Some "list"
  | "FStar.Pervasives.Native.option" -> FStar_Pervasives_Native.Some "option"
  | "FStar.Char.char" -> FStar_Pervasives_Native.Some "FStar_Char.char"
  | uu___ -> FStar_Pervasives_Native.None
let is_builtin_type (n : FStarC_Custard_Syntax.name) : Prims.bool=
  let uu___ = builtin_type n in
  match uu___ with | FStar_Pervasives_Native.Some v -> true | uu___1 -> false
let int_module_stem (s : FStarC_Const.signedness) : Prims.string=
  match s with
  | FStarC_Const.Unsigned -> "UInt"
  | FStarC_Const.Signed -> "Int"
let int_module
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      (match w with
       | FStarC_Custard_Syntax.WSizet -> "FStar_SizeT"
       | FStarC_Custard_Syntax.W128 ->
           FStarC_Effect.failwith
             "Custard: a 128-bit machine integer reached the OCaml backend"
       | uu___1 ->
           Prims.strcat "FStar_"
             (Prims.strcat (int_module_stem s)
                (match w with
                 | FStarC_Custard_Syntax.W8 -> "8"
                 | FStarC_Custard_Syntax.W16 -> "16"
                 | FStarC_Custard_Syntax.W32 -> "32"
                 | FStarC_Custard_Syntax.W64 -> "64"
                 | FStarC_Custard_Syntax.W128 -> "SizeT"
                 | FStarC_Custard_Syntax.WSizet -> "SizeT")))
let int_cast_stem
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      let uu___1 =
        match w with
        | FStarC_Custard_Syntax.W8 -> "8"
        | FStarC_Custard_Syntax.W16 -> "16"
        | FStarC_Custard_Syntax.W32 -> "32"
        | FStarC_Custard_Syntax.W64 -> "64"
        | FStarC_Custard_Syntax.W128 ->
            FStarC_Effect.failwith
              "Custard: a 128-bit machine integer reached the OCaml backend"
        | FStarC_Custard_Syntax.WSizet ->
            FStarC_Effect.failwith
              "Custard: FStar.SizeT has no FStar.Int.Cast conversion" in
      Prims.strcat
        (match s with
         | FStarC_Const.Unsigned -> "uint"
         | FStarC_Const.Signed -> "int") uu___1
let int_inj (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.string=
  let uu___ = sw in
  match uu___ with
  | (sgn, uu___1) ->
      let uu___2 = int_module sw in
      Prims.strcat uu___2
        (match sgn with
         | FStarC_Const.Unsigned -> ".uint_to_t"
         | FStarC_Const.Signed -> ".int_to_t")
let reject_fwidth (fw : FStarC_Custard_Syntax.fwidth) : unit=
  if match fw with | FStarC_Custard_Syntax.Float64 -> true | uu___ -> false
  then ()
  else
    (let format =
       match fw with
       | FStarC_Custard_Syntax.Float32 -> "binary32"
       | FStarC_Custard_Syntax.Float64 -> "binary64"
       | FStarC_Custard_Syntax.Float16 -> "binary16"
       | FStarC_Custard_Syntax.BFloat16 -> "bfloat16" in
     let what =
       match fw with
       | FStarC_Custard_Syntax.Float32 -> "FStar.Float32"
       | uu___ -> format in
     FStarC_Errors.raise_error0
       FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic
          [FStarC_Errors_Msg.text
             (Prims.strcat "Custard: "
                (Prims.strcat what " has no OCaml representation."));
          FStarC_Errors_Msg.text
            (Prims.strcat
               "OCaml's float is IEEE 754 binary64 and there is no "
               (Prims.strcat format
                  " type to round to, so such a program would silently compute at double precision (sections 38 and 66)."));
          FStarC_Errors_Msg.text
            "Use FStar.Float64, or extract with --custard_backend C."]))
let rec ty (t : FStarC_Custard_Syntax.cty) : Prims.string=
  match t with
  | FStarC_Custard_Syntax.TUnit -> "unit"
  | FStarC_Custard_Syntax.TExn -> "exn"
  | FStarC_Custard_Syntax.TAny -> "Obj.t"
  | FStarC_Custard_Syntax.TVar x ->
      let uu___ = ocaml_var x in Prims.strcat "'" uu___
  | FStarC_Custard_Syntax.TInt sw ->
      let uu___ = int_module sw in Prims.strcat uu___ ".t"
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float64) -> "float"
  | FStarC_Custard_Syntax.TFloat fw -> (reject_fwidth fw; "float")
  | FStarC_Custard_Syntax.TArrow (t1, uu___, t2) ->
      let uu___1 =
        let uu___2 = ty t1 in
        let uu___3 =
          let uu___4 = let uu___5 = ty t2 in Prims.strcat uu___5 ")" in
          Prims.strcat " -> " uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat "(" uu___1
  | FStarC_Custard_Syntax.TTuple ts ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map ty ts in
          FStarC_String.concat " * " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TBuf t1 ->
      let uu___ = let uu___1 = ty t1 in Prims.strcat uu___1 " array)" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TRef t1 ->
      let uu___ = let uu___1 = ty t1 in Prims.strcat uu___1 " ref)" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TInline uu___ ->
      FStarC_Effect.failwith
        "Custard: an inline-field marker reached the OCaml backend"
  | FStarC_Custard_Syntax.TConst uu___ ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [FStarC_Errors_Msg.text
              "Custard: an external type with a template target reached the OCaml backend.";
           FStarC_Errors_Msg.text
             "[wmma::fragment<matrix_a, 16, 16, 16, half, row_major>] is one type and [wmma::fragment<matrix_b, ...>] another; OCaml has no such construction, so section 69 is a C-backend feature (--custard_backend C).";
           FStarC_Errors_Msg.text
             "The unparameterized form still works everywhere: a [@@custard_extern] target with no [{0}] placeholder names one target type, and its arguments are dropped."])
  | FStarC_Custard_Syntax.TApp (n, args) when
      let uu___ = is_tuple_type n in
      if uu___
      then match args with | hd::tl -> true | uu___1 -> false
      else false ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map ty args in
          FStarC_String.concat " * " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TApp (n, []) ->
      let uu___ = builtin_type n in
      (match uu___ with
       | FStar_Pervasives_Native.Some s -> s
       | FStar_Pervasives_Native.None ->
           let uu___1 = ocaml_type_name n in qualify n uu___1)
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let hd =
        let uu___ = builtin_type n in
        match uu___ with
        | FStar_Pervasives_Native.Some s -> s
        | FStar_Pervasives_Native.None ->
            let uu___1 = ocaml_type_name n in qualify n uu___1 in
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map ty args in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 (Prims.strcat ") " hd) in
      Prims.strcat "(" uu___
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
        if (i < (Prims.of_int 32)) || (i = (Prims.of_int 127))
        then
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
            Prims.strcat (if i < (Prims.of_int 10) then "00" else "0") uu___1 in
          Prims.strcat "\\" uu___
        else FStarC_Util.string_of_char c1 in
  let uu___ = FStarC_List.map esc (FStarC_String.list_of_string s) in
  FStarC_String.concat "" uu___
let constant (c : FStarC_Custard_Syntax.constant) : Prims.string=
  match c with
  | FStarC_Custard_Syntax.CUnit -> "()"
  | FStarC_Custard_Syntax.CBool b -> if b then "true" else "false"
  | FStarC_Custard_Syntax.CFloat (FStarC_Custard_Syntax.FLNan, fw) ->
      (reject_fwidth fw; "(Stdlib.nan)")
  | FStarC_Custard_Syntax.CFloat (FStarC_Custard_Syntax.FLInf neg, fw) ->
      (reject_fwidth fw;
       if neg then "(Stdlib.neg_infinity)" else "(Stdlib.infinity)")
  | FStarC_Custard_Syntax.CFloat (v, fw) ->
      (reject_fwidth fw;
       Prims.strcat "("
         (Prims.strcat (FStarC_Custard_Syntax.float_lit_to_string v) ")"))
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.None) ->
      Prims.strcat "(Prims.parse_int \""
        (Prims.strcat (FStarC_Custard_Syntax.int_lit_to_string v b) "\")")
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.Some sw) ->
      let uu___ =
        let uu___1 = int_inj sw in
        Prims.strcat uu___1
          (Prims.strcat " (Prims.parse_int \""
             (Prims.strcat (FStarC_Custard_Syntax.int_lit_to_string v b)
                "\"))")) in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.CChar c1 ->
      FStarC_Class_Show.show FStarC_Class_Show.showable_int
        (FStarC_Util.int_of_char c1)
  | FStarC_Custard_Syntax.CString s ->
      let uu___ = let uu___1 = escape s in Prims.strcat uu___1 "\"" in
      Prims.strcat "\"" uu___
let op_name (o : FStarC_Custard_Syntax.prim_op) : Prims.string=
  match o.FStarC_Custard_Syntax.po_ty with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat fw) ->
      (reject_fwidth fw;
       (match o.FStarC_Custard_Syntax.po_op with
        | FStarC_Custard_Syntax.Add -> "( +. )"
        | FStarC_Custard_Syntax.AddW -> "( +. )"
        | FStarC_Custard_Syntax.Sub -> "( -. )"
        | FStarC_Custard_Syntax.SubW -> "( -. )"
        | FStarC_Custard_Syntax.Mult -> "( *. )"
        | FStarC_Custard_Syntax.MultW -> "( *. )"
        | FStarC_Custard_Syntax.Div -> "( /. )"
        | FStarC_Custard_Syntax.DivW -> "( /. )"
        | FStarC_Custard_Syntax.Eq -> "( = )"
        | FStarC_Custard_Syntax.Neq -> "( <> )"
        | FStarC_Custard_Syntax.Lt -> "( < )"
        | FStarC_Custard_Syntax.Lte -> "( <= )"
        | FStarC_Custard_Syntax.Gt -> "( > )"
        | FStarC_Custard_Syntax.Gte -> "( >= )"
        | uu___1 ->
            FStarC_Effect.failwith
              "Custard: no OCaml float operator for this operation"))
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw) ->
      let uu___ = int_module sw in
      let uu___1 =
        let uu___2 =
          match o.FStarC_Custard_Syntax.po_op with
          | FStarC_Custard_Syntax.Add -> "add"
          | FStarC_Custard_Syntax.AddW -> "add_mod"
          | FStarC_Custard_Syntax.Sub -> "sub"
          | FStarC_Custard_Syntax.SubW -> "sub_mod"
          | FStarC_Custard_Syntax.Mult -> "mul"
          | FStarC_Custard_Syntax.MultW -> "mul_mod"
          | FStarC_Custard_Syntax.Div -> "div"
          | FStarC_Custard_Syntax.DivW -> "div"
          | FStarC_Custard_Syntax.Mod -> "rem"
          | FStarC_Custard_Syntax.BOr -> "logor"
          | FStarC_Custard_Syntax.BAnd -> "logand"
          | FStarC_Custard_Syntax.BXor -> "logxor"
          | FStarC_Custard_Syntax.BNot -> "lognot"
          | FStarC_Custard_Syntax.BShiftL -> "shift_left"
          | FStarC_Custard_Syntax.BShiftR -> "shift_right"
          | FStarC_Custard_Syntax.Eq -> "eq"
          | FStarC_Custard_Syntax.Neq -> "ne"
          | FStarC_Custard_Syntax.Lt -> "lt"
          | FStarC_Custard_Syntax.Lte -> "lte"
          | FStarC_Custard_Syntax.Gt -> "gt"
          | FStarC_Custard_Syntax.Gte -> "gte"
          | FStarC_Custard_Syntax.And -> "logand"
          | FStarC_Custard_Syntax.Or -> "logor"
          | FStarC_Custard_Syntax.Not -> "lognot"
          | FStarC_Custard_Syntax.BufRead ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufWrite ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufSub ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufFree ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufNull ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufIsNull ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufBlit ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufCreate uu___3 ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufLit ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.BufUnconst ->
              FStarC_Effect.failwith
                "Custard: a buffer operation is not an OCaml operator"
          | FStarC_Custard_Syntax.Commented uu___3 ->
              FStarC_Effect.failwith
                "Custard: a comment is not an OCaml operator" in
        Prims.strcat "." uu___2 in
      Prims.strcat uu___ uu___1
  | FStar_Pervasives_Native.None ->
      (match o.FStarC_Custard_Syntax.po_op with
       | FStarC_Custard_Syntax.Add -> "Prims.op_Plus"
       | FStarC_Custard_Syntax.AddW -> "Prims.op_Plus"
       | FStarC_Custard_Syntax.Sub -> "Prims.op_Minus"
       | FStarC_Custard_Syntax.SubW -> "Prims.op_Minus"
       | FStarC_Custard_Syntax.Mult -> "Prims.op_Star"
       | FStarC_Custard_Syntax.MultW -> "Prims.op_Star"
       | FStarC_Custard_Syntax.Div -> "Prims.op_Slash"
       | FStarC_Custard_Syntax.DivW -> "Prims.op_Slash"
       | FStarC_Custard_Syntax.Mod -> "Prims.op_Percent"
       | FStarC_Custard_Syntax.Eq -> "(=)"
       | FStarC_Custard_Syntax.Neq -> "(<>)"
       | FStarC_Custard_Syntax.Lt -> "(<)"
       | FStarC_Custard_Syntax.Lte -> "(<=)"
       | FStarC_Custard_Syntax.Gt -> "(>)"
       | FStarC_Custard_Syntax.Gte -> "(>=)"
       | FStarC_Custard_Syntax.And -> "(&&)"
       | FStarC_Custard_Syntax.Or -> "(||)"
       | FStarC_Custard_Syntax.Not -> "not"
       | FStarC_Custard_Syntax.BOr -> "(lor)"
       | FStarC_Custard_Syntax.BAnd -> "(land)"
       | FStarC_Custard_Syntax.BXor -> "(lxor)"
       | FStarC_Custard_Syntax.BNot -> "lnot"
       | FStarC_Custard_Syntax.BShiftL -> "(lsl)"
       | FStarC_Custard_Syntax.BShiftR -> "(lsr)"
       | FStarC_Custard_Syntax.BufRead ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufWrite ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufSub ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufFree ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufNull ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufIsNull ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufBlit ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufCreate uu___ ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufLit ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.BufUnconst ->
           FStarC_Effect.failwith
             "Custard: a buffer operation is not an OCaml operator"
       | FStarC_Custard_Syntax.Commented uu___ ->
           FStarC_Effect.failwith
             "Custard: a comment is not an OCaml operator")
let rec defer_ints (n : Prims.int) (p : FStarC_Custard_Syntax.pat) :
  (Prims.int * FStarC_Custard_Syntax.pat * (Prims.string *
    FStarC_Custard_Syntax.constant) Prims.list)=
  match p with
  | FStarC_Custard_Syntax.PConst c when
      match c with
      | FStarC_Custard_Syntax.CInt uu___ -> true
      | uu___ -> false ->
      let x = Prims.strcat "_iconst" (Prims.string_of_int n) in
      ((n + Prims.int_one), (FStarC_Custard_Syntax.PVar x), [(x, c)])
  | FStarC_Custard_Syntax.PCtor (nm, ps) ->
      let uu___ = defer_ints_list n ps in
      (match uu___ with
       | (n1, ps1, eqs) -> (n1, (FStarC_Custard_Syntax.PCtor (nm, ps1)), eqs))
  | FStarC_Custard_Syntax.PRecord (nm, fs) ->
      let uu___ = defer_ints_fields n fs in
      (match uu___ with
       | (n1, fs1, eqs) ->
           (n1, (FStarC_Custard_Syntax.PRecord (nm, fs1)), eqs))
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ = defer_ints_list n ps in
      (match uu___ with
       | (n1, ps1, eqs) -> (n1, (FStarC_Custard_Syntax.PTuple ps1), eqs))
  | uu___ -> (n, p, [])
and defer_ints_fields (n : Prims.int)
  (fs : (Prims.string * FStarC_Custard_Syntax.pat) Prims.list) :
  (Prims.int * (Prims.string * FStarC_Custard_Syntax.pat) Prims.list *
    (Prims.string * FStarC_Custard_Syntax.constant) Prims.list)=
  match fs with
  | [] -> (n, [], [])
  | (f, p)::fs1 ->
      let uu___ = defer_ints n p in
      (match uu___ with
       | (n1, p1, eqs) ->
           let uu___1 = defer_ints_fields n1 fs1 in
           (match uu___1 with
            | (n2, fs2, eqs') ->
                (n2, ((f, p1) :: fs2), (FStarC_List.op_At eqs eqs'))))
and defer_ints_list (n : Prims.int)
  (ps : FStarC_Custard_Syntax.pat Prims.list) :
  (Prims.int * FStarC_Custard_Syntax.pat Prims.list * (Prims.string *
    FStarC_Custard_Syntax.constant) Prims.list)=
  match ps with
  | [] -> (n, [], [])
  | p::ps1 ->
      let uu___ = defer_ints n p in
      (match uu___ with
       | (n1, p1, eqs) ->
           let uu___1 = defer_ints_list n1 ps1 in
           (match uu___1 with
            | (n2, ps2, eqs') ->
                (n2, (p1 :: ps2), (FStarC_List.op_At eqs eqs'))))
let rec pattern (p : FStarC_Custard_Syntax.pat) : Prims.string=
  match p with
  | FStarC_Custard_Syntax.PWild -> "_"
  | FStarC_Custard_Syntax.PVar x -> ocaml_local x
  | FStarC_Custard_Syntax.PConst c -> constant c
  | FStarC_Custard_Syntax.PCtor (n, []) -> ctor_ref n
  | FStarC_Custard_Syntax.PCtor (n, p1::p2::[]) when
      let uu___ = builtin_ctor n in
      uu___ = (FStar_Pervasives_Native.Some "::") ->
      let uu___ =
        let uu___1 = pattern p1 in
        let uu___2 =
          let uu___3 = let uu___4 = pattern p2 in Prims.strcat uu___4 ")" in
          Prims.strcat " :: " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.PCtor (n, ps) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map pattern ps in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.PCtor (n, ps) ->
      let uu___ =
        let uu___1 = ctor_ref n in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map pattern ps in
              FStarC_String.concat ", " uu___5 in
            Prims.strcat uu___4 "))" in
          Prims.strcat " (" uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.PRecord (n, fs) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let k =
        let uu___ = tuple_arity n in
        match uu___ with | FStar_Pervasives_Native.Some v -> v in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (f, p1) -> let uu___5 = pattern p1 in (f, uu___5)) fs in
            by_position k "_" uu___3 in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.PRecord (n, fs) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.mapi
              (fun i uu___3 ->
                 match uu___3 with
                 | (f, p1) ->
                     let uu___4 =
                       if i = Prims.int_zero
                       then let uu___5 = ocaml_var f in qualify n uu___5
                       else ocaml_var f in
                     let uu___5 =
                       let uu___6 = pattern p1 in Prims.strcat " = " uu___6 in
                     Prims.strcat uu___4 uu___5) fs in
          FStarC_String.concat "; " uu___2 in
        Prims.strcat uu___1
          (if match fs with | hd::tl -> true | uu___2 -> false
           then "; _ }"
           else "_ }") in
      Prims.strcat "{ " uu___
  | FStarC_Custard_Syntax.PTuple ps ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map pattern ps in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.POr ps ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map pattern ps in
          FStarC_String.concat " | " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
and ctor_ref (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ = builtin_ctor n in
  match uu___ with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None ->
      let uu___1 = ocaml_ctor_ident n in qualify n uu___1
and builtin_ctor (n : FStarC_Custard_Syntax.name) :
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
  | "Prims.Nil" -> FStar_Pervasives_Native.Some "[]"
  | "Prims.Cons" -> FStar_Pervasives_Native.Some "::"
  | "FStar.Pervasives.Native.None" -> FStar_Pervasives_Native.Some "None"
  | "FStar.Pervasives.Native.Some" -> FStar_Pervasives_Native.Some "Some"
  | uu___ -> FStar_Pervasives_Native.None
let ascribe_record (n : FStarC_Custard_Syntax.name)
  (fs : Prims.string Prims.list) (s : Prims.string) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang record_params in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with
  | uu___1 when
      let uu___2 = FStarC_List.existsb (ambiguous_label n) fs in
      Prims.not uu___2 -> s
  | FStar_Pervasives_Native.None -> s
  | FStar_Pervasives_Native.Some k ->
      let rec wilds i =
        if i <= Prims.int_zero
        then []
        else (let uu___1 = wilds (i - Prims.int_one) in "_" :: uu___1) in
      let args =
        if k = Prims.int_zero
        then ""
        else
          if k = Prims.int_one
          then "_ "
          else
            (let uu___1 =
               let uu___2 =
                 let uu___3 = wilds k in FStarC_String.concat ", " uu___3 in
               Prims.strcat uu___2 ") " in
             Prims.strcat "(" uu___1) in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = let uu___6 = ocaml_type_name n in qualify n uu___6 in
              Prims.strcat uu___5 ")" in
            Prims.strcat args uu___4 in
          Prims.strcat " : " uu___3 in
        Prims.strcat s uu___2 in
      Prims.strcat "(" uu___1
let line_width : Prims.int= Prims.of_int 80
let value_preserving
  (a : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (b : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.bool=
  let uu___ = a in
  match uu___ with
  | (sa, wa) ->
      let uu___1 = b in
      (match uu___1 with
       | (sb, wb) ->
           (match (sa, sb) with
            | (FStarC_Const.Unsigned, FStarC_Const.Unsigned) ->
                (FStarC_Custard_Syntax.width_bits wa) <=
                  (FStarC_Custard_Syntax.width_bits wb)
            | (FStarC_Const.Signed, FStarC_Const.Signed) ->
                (FStarC_Custard_Syntax.width_bits wa) <=
                  (FStarC_Custard_Syntax.width_bits wb)
            | (FStarC_Const.Unsigned, FStarC_Const.Signed) ->
                (FStarC_Custard_Syntax.width_bits wa) <
                  (FStarC_Custard_Syntax.width_bits wb)
            | (FStarC_Const.Signed, FStarC_Const.Unsigned) -> false))
let rec term (ind : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst c -> constant c
  | FStarC_Custard_Syntax.EVar x -> ocaml_local x
  | FStarC_Custard_Syntax.EQual (n, uu___) ->
      let uu___1 = external_target n in
      (match uu___1 with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None ->
           let uu___2 = ocaml_value_name n in qualify n uu___2)
  | FStarC_Custard_Syntax.ECtor (n, []) -> ctor_ref n
  | FStarC_Custard_Syntax.ECtor (n, a::b::[]) when
      let uu___ = builtin_ctor n in
      uu___ = (FStar_Pervasives_Native.Some "::") ->
      let uu___ =
        let uu___1 = term ind a in
        let uu___2 =
          let uu___3 = let uu___4 = term ind b in Prims.strcat uu___4 ")" in
          Prims.strcat " :: " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.ECtor (n, args) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (term ind) args in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.ECtor (n, args) ->
      let uu___ =
        let uu___1 = ctor_ref n in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map (term ind) args in
              FStarC_String.concat ", " uu___5 in
            Prims.strcat uu___4 "))" in
          Prims.strcat " (" uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.ETuple es ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (term ind) es in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EApp (hd, args) ->
      let uu___ =
        let uu___1 = term ind hd in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map (term ind) args in
              FStarC_String.concat " " uu___5 in
            Prims.strcat uu___4 ")" in
          Prims.strcat " " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EFun (bs, body) ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.map
              (fun b -> ocaml_local b.FStarC_Custard_Syntax.b_name) bs in
          FStarC_String.concat " " uu___2 in
        let uu___2 =
          let uu___3 = let uu___4 = term ind body in Prims.strcat uu___4 ")" in
          Prims.strcat " -> " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(fun " uu___
  | FStarC_Custard_Syntax.ELet uu___ ->
      let uu___1 = let uu___2 = stmts ind e in Prims.strcat uu___2 ")" in
      Prims.strcat "(" uu___1
  | FStarC_Custard_Syntax.ESeq uu___ ->
      let uu___1 = let uu___2 = stmts ind e in Prims.strcat uu___2 ")" in
      Prims.strcat "(" uu___1
  | FStarC_Custard_Syntax.EIf (c, t, f) ->
      let uu___ =
        let uu___1 = term ind c in
        let uu___2 =
          let uu___3 =
            let uu___4 = term ind t in
            let uu___5 =
              let uu___6 = let uu___7 = term ind f in Prims.strcat uu___7 ")" in
              Prims.strcat " else " uu___6 in
            Prims.strcat uu___4 uu___5 in
          Prims.strcat " then " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(if " uu___
  | FStarC_Custard_Syntax.EMatch (scrut, brs) ->
      let ind' = Prims.strcat ind "  " in
      let uu___ =
        let uu___1 = term ind scrut in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map (case ind') brs in
              FStarC_String.concat "" uu___5 in
            Prims.strcat uu___4 (Prims.strcat ind ")") in
          Prims.strcat " with\n" uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(match " uu___
  | FStarC_Custard_Syntax.ERecord (n, fs) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let k =
        let uu___ = tuple_arity n in
        match uu___ with | FStar_Pervasives_Native.Some v -> v in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_List.map
                (fun uu___4 ->
                   match uu___4 with
                   | (f, e1) -> let uu___5 = term ind e1 in (f, uu___5)) fs in
            by_position k "(Obj.magic ())" uu___3 in
          FStarC_String.concat ", " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.ERecord (n, fs) ->
      let ind' = Prims.strcat ind "  " in
      let parts =
        FStarC_List.mapi
          (fun i uu___ ->
             match uu___ with
             | (f, e1) ->
                 let uu___1 =
                   if i = Prims.int_zero
                   then let uu___2 = ocaml_var f in qualify n uu___2
                   else ocaml_var f in
                 let uu___2 =
                   let uu___3 = term ind' e1 in Prims.strcat " = " uu___3 in
                 Prims.strcat uu___1 uu___2) fs in
      let one =
        Prims.strcat "{ "
          (Prims.strcat (FStarC_String.concat "; " parts) " }") in
      let body =
        let uu___ =
          if
            ((FStarC_String.length ind) + (FStarC_String.length one)) <=
              line_width
          then
            let uu___1 =
              FStarC_List.existsb (fun c -> c = 10)
                (FStarC_String.list_of_string one) in
            Prims.not uu___1
          else false in
        if uu___
        then one
        else
          Prims.strcat "{ "
            (Prims.strcat
               (FStarC_String.concat (Prims.strcat ";\n" ind') parts) " }") in
      let uu___ = FStarC_List.map FStar_Pervasives_Native.fst fs in
      ascribe_record n uu___ body
  | FStarC_Custard_Syntax.EProj (e1, n, f) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let k =
        let uu___ = tuple_arity n in
        match uu___ with | FStar_Pervasives_Native.Some v -> v in
      let uu___ =
        let uu___1 = term ind e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = by_position k "_" [(f, "custard_tup")] in
              FStarC_String.concat ", " uu___5 in
            Prims.strcat uu___4 ") -> custard_tup)" in
          Prims.strcat " with (" uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(match " uu___
  | FStarC_Custard_Syntax.EProj (e1, n, f) ->
      let uu___ =
        let uu___1 = let uu___2 = term ind e1 in ascribe_record n [f] uu___2 in
        let uu___2 =
          let uu___3 = let uu___4 = ocaml_var f in qualify n uu___4 in
          Prims.strcat ")." uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EDiscrim (uu___, n) when
      let uu___1 = tuple_arity n in
      match uu___1 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___2 -> false -> "true"
  | FStarC_Custard_Syntax.EDiscrim (e1, n) ->
      let uu___ =
        let uu___1 = term ind e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = ctor_ref n in
            Prims.strcat uu___4 " _ -> true | _ -> false)" in
          Prims.strcat " with " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(match " uu___
  | FStarC_Custard_Syntax.ECast (e1, t) ->
      (match ((e1.FStarC_Custard_Syntax.ty), t) with
       | (FStarC_Custard_Syntax.TInt sw1, FStarC_Custard_Syntax.TInt sw2)
           when sw1 = sw2 -> term ind e1
       | (FStarC_Custard_Syntax.TInt sw1, FStarC_Custard_Syntax.TFloat uu___)
           ->
           let uu___1 =
             let uu___2 = int_module sw1 in
             let uu___3 =
               let uu___4 =
                 let uu___5 = term ind e1 in Prims.strcat uu___5 "))" in
               Prims.strcat ".v " uu___4 in
             Prims.strcat uu___2 uu___3 in
           Prims.strcat "(Z.to_float (" uu___1
       | (FStarC_Custard_Syntax.TFloat uu___, FStarC_Custard_Syntax.TFloat
          uu___1) -> term ind e1
       | (FStarC_Custard_Syntax.TInt sw1, FStarC_Custard_Syntax.TInt sw2)
           when
           ((FStar_Pervasives_Native.snd sw1) <> FStarC_Custard_Syntax.WSizet)
             &&
             ((FStar_Pervasives_Native.snd sw2) <>
                FStarC_Custard_Syntax.WSizet)
           ->
           let uu___ =
             let uu___1 = int_cast_stem sw1 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = int_cast_stem sw2 in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = term ind e1 in Prims.strcat uu___7 ")" in
                   Prims.strcat " " uu___6 in
                 Prims.strcat uu___4 uu___5 in
               Prims.strcat "_to_" uu___3 in
             Prims.strcat uu___1 uu___2 in
           Prims.strcat "(FStar_Int_Cast." uu___
       | (FStarC_Custard_Syntax.TInt sw1, FStarC_Custard_Syntax.TInt sw2) ->
           let uu___ =
             let uu___1 = int_inj sw2 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = int_module sw1 in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = term ind e1 in Prims.strcat uu___7 "))" in
                   Prims.strcat ".v " uu___6 in
                 Prims.strcat uu___4 uu___5 in
               Prims.strcat " (" uu___3 in
             Prims.strcat uu___1 uu___2 in
           Prims.strcat "(" uu___
       | uu___ -> coerce ind e1 t)
  | FStarC_Custard_Syntax.ECoerce (e1, t) -> coerce ind e1 t
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufCreate uu___;
         FStarC_Custard_Syntax.po_ty = uu___1;_},
       init::len::[])
      ->
      if
        (match e.FStarC_Custard_Syntax.ty with
         | FStarC_Custard_Syntax.TRef _0 -> true
         | uu___2 -> false)
      then
        let uu___2 = let uu___3 = term ind init in Prims.strcat uu___3 ")" in
        Prims.strcat "(ref " uu___2
      else
        (let uu___2 =
           let uu___3 = index ind len in
           let uu___4 =
             let uu___5 =
               let uu___6 = term ind init in Prims.strcat uu___6 ")" in
             Prims.strcat " " uu___5 in
           Prims.strcat uu___3 uu___4 in
         Prims.strcat "(Array.make " uu___2)
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufRead;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::i::[])
      ->
      if
        (match b.FStarC_Custard_Syntax.ty with
         | FStarC_Custard_Syntax.TRef _0 -> true
         | uu___1 -> false)
      then
        let uu___1 = let uu___2 = term ind b in Prims.strcat uu___2 "))" in
        Prims.strcat "(!(" uu___1
      else
        (let uu___1 =
           let uu___2 = term ind b in
           let uu___3 =
             let uu___4 = let uu___5 = index ind i in Prims.strcat uu___5 ")" in
             Prims.strcat ").(" uu___4 in
           Prims.strcat uu___2 uu___3 in
         Prims.strcat "(" uu___1)
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufWrite;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::i::v::[])
      ->
      if
        (match b.FStarC_Custard_Syntax.ty with
         | FStarC_Custard_Syntax.TRef _0 -> true
         | uu___1 -> false)
      then
        let uu___1 =
          let uu___2 = term ind b in
          let uu___3 =
            let uu___4 = let uu___5 = term ind v in Prims.strcat uu___5 ")" in
            Prims.strcat ") := " uu___4 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat "((" uu___1
      else
        (let uu___1 =
           let uu___2 = term ind b in
           let uu___3 =
             let uu___4 =
               let uu___5 = index ind i in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = term ind v in Prims.strcat uu___8 ")" in
                 Prims.strcat ") <- " uu___7 in
               Prims.strcat uu___5 uu___6 in
             Prims.strcat ").(" uu___4 in
           Prims.strcat uu___2 uu___3 in
         Prims.strcat "((" uu___1)
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufFree;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1::[])
      -> "()"
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufNull;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       [])
      ->
      if
        (match e.FStarC_Custard_Syntax.ty with
         | FStarC_Custard_Syntax.TRef _0 -> true
         | uu___1 -> false)
      then "(Obj.magic 0)"
      else "[||]"
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufIsNull;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      ->
      if
        (match b.FStarC_Custard_Syntax.ty with
         | FStarC_Custard_Syntax.TRef _0 -> true
         | uu___1 -> false)
      then
        let uu___1 = let uu___2 = term ind b in Prims.strcat uu___2 ")))" in
        Prims.strcat "(not (Obj.is_block (Obj.repr " uu___1
      else
        (let uu___1 = let uu___2 = term ind b in Prims.strcat uu___2 ") = 0)" in
         Prims.strcat "(Array.length (" uu___1)
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufBlit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       src::si::dst::di::len::[])
      ->
      let uu___1 =
        let uu___2 = term ind src in
        let uu___3 =
          let uu___4 =
            let uu___5 = index ind si in
            let uu___6 =
              let uu___7 =
                let uu___8 = term ind dst in
                let uu___9 =
                  let uu___10 =
                    let uu___11 = index ind di in
                    let uu___12 =
                      let uu___13 =
                        let uu___14 = index ind len in
                        Prims.strcat uu___14 ")" in
                      Prims.strcat " " uu___13 in
                    Prims.strcat uu___11 uu___12 in
                  Prims.strcat " " uu___10 in
                Prims.strcat uu___8 uu___9 in
              Prims.strcat " " uu___7 in
            Prims.strcat uu___5 uu___6 in
          Prims.strcat " " uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat "(Array.blit " uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufSub;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      ->
      "(failwith \"Custard: pointer arithmetic has no OCaml representation\")"
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       elems)
      ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_List.map (term ind) elems in
          FStarC_String.concat "; " uu___3 in
        Prims.strcat uu___2 " |]" in
      Prims.strcat "[| " uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufUnconst;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      -> term ind b
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
      -> Prims.strcat "((* " (Prims.strcat before " *) ())")
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
            let uu___4 = term ind b in
            Prims.strcat uu___4
              (Prims.strcat " (* " (Prims.strcat after " *))")) in
          Prims.strcat " *) " uu___3 in
        Prims.strcat before uu___2 in
      Prims.strcat "((* " uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.And;
         FStarC_Custard_Syntax.po_ty = FStar_Pervasives_Native.None;_},
       a::b::[])
      ->
      let uu___ =
        let uu___1 = term ind a in
        let uu___2 =
          let uu___3 = let uu___4 = term ind b in Prims.strcat uu___4 ")" in
          Prims.strcat " && " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.Or;
         FStarC_Custard_Syntax.po_ty = FStar_Pervasives_Native.None;_},
       a::b::[])
      ->
      let uu___ =
        let uu___1 = term ind a in
        let uu___2 =
          let uu___3 = let uu___4 = term ind b in Prims.strcat uu___4 ")" in
          Prims.strcat " || " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EOp (op, args) ->
      let uu___ =
        let uu___1 = op_name op in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map (term ind) args in
              FStarC_String.concat " " uu___5 in
            Prims.strcat uu___4 ")" in
          Prims.strcat " " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EAny -> "(Obj.magic 0)"
  | FStarC_Custard_Syntax.EAbort s ->
      let uu___ = let uu___1 = escape s in Prims.strcat uu___1 "\")" in
      Prims.strcat "(failwith \"" uu___
  | FStarC_Custard_Syntax.EWhile (c, body) ->
      let uu___ =
        let uu___1 = term ind c in
        let uu___2 =
          let uu___3 =
            let uu___4 = term ind body in Prims.strcat uu___4 " done)" in
          Prims.strcat " do " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(while " uu___
  | FStarC_Custard_Syntax.ERaise e1 ->
      let uu___ = let uu___1 = term ind e1 in Prims.strcat uu___1 ")" in
      Prims.strcat "(raise " uu___
  | FStarC_Custard_Syntax.ETry (e1, brs) ->
      let ind' = Prims.strcat ind "  " in
      let uu___ =
        let uu___1 = term ind e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_List.map (case ind') brs in
              FStarC_String.concat "" uu___5 in
            Prims.strcat uu___4 (Prims.strcat ind ")") in
          Prims.strcat " with\n" uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(try " uu___
and coerce (ind : Prims.string) (e1 : FStarC_Custard_Syntax.expr)
  (t : FStarC_Custard_Syntax.cty) : Prims.string=
  match ((e1.FStarC_Custard_Syntax.ty), t) with
  | (FStarC_Custard_Syntax.TInt uu___, FStarC_Custard_Syntax.TAny) ->
      let uu___1 = let uu___2 = term ind e1 in Prims.strcat uu___2 "))" in
      Prims.strcat "(Obj.magic (" uu___1
  | (FStarC_Custard_Syntax.TAny, FStarC_Custard_Syntax.TInt uu___) ->
      let uu___1 = let uu___2 = term ind e1 in Prims.strcat uu___2 "))" in
      Prims.strcat "(Obj.magic (" uu___1
  | (FStarC_Custard_Syntax.TInt sw1, uu___) ->
      let uu___1 =
        let uu___2 = int_module sw1 in
        let uu___3 =
          let uu___4 = let uu___5 = term ind e1 in Prims.strcat uu___5 "))" in
          Prims.strcat ".v " uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat "(Obj.magic (" uu___1
  | (uu___, FStarC_Custard_Syntax.TInt sw2) ->
      let uu___1 =
        let uu___2 = int_inj sw2 in
        let uu___3 =
          let uu___4 = let uu___5 = term ind e1 in Prims.strcat uu___5 ")))" in
          Prims.strcat " (Obj.magic (" uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat "(" uu___1
  | uu___ ->
      let uu___1 = let uu___2 = term ind e1 in Prims.strcat uu___2 "))" in
      Prims.strcat "(Obj.magic (" uu___1
and index (ind : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt (v, b, uu___))
      -> FStarC_Custard_Syntax.int_lit_to_string v b
  | FStarC_Custard_Syntax.ECoerce (e1, uu___) -> index ind e1
  | FStarC_Custard_Syntax.ECast (e1, t) when
      match ((e1.FStarC_Custard_Syntax.ty), t) with
      | (FStarC_Custard_Syntax.TInt a, FStarC_Custard_Syntax.TInt b) ->
          value_preserving a b
      | uu___ -> false -> index ind e1
  | uu___ ->
      (match e.FStarC_Custard_Syntax.ty with
       | FStarC_Custard_Syntax.TInt sw ->
           let uu___1 =
             let uu___2 = int_module sw in
             let uu___3 =
               let uu___4 =
                 let uu___5 = term ind e in Prims.strcat uu___5 "))" in
               Prims.strcat ".v " uu___4 in
             Prims.strcat uu___2 uu___3 in
           Prims.strcat "(Z.to_int (" uu___1
       | uu___1 ->
           let uu___2 = let uu___3 = term ind e in Prims.strcat uu___3 "))" in
           Prims.strcat "(Obj.magic (" uu___2)
and stmts (ind : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet (x, uu___, e1, e2) ->
      let uu___1 =
        let uu___2 = ocaml_local x in
        let uu___3 =
          let uu___4 =
            let uu___5 = term (Prims.strcat ind "  ") e1 in
            let uu___6 =
              let uu___7 =
                let uu___8 = stmts ind e2 in Prims.strcat ind uu___8 in
              Prims.strcat " in\n" uu___7 in
            Prims.strcat uu___5 uu___6 in
          Prims.strcat " = " uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat "let " uu___1
  | FStarC_Custard_Syntax.ESeq (e1, e2) ->
      let s = term ind e1 in
      let s1 =
        if
          match e1.FStarC_Custard_Syntax.ty with
          | FStarC_Custard_Syntax.TUnit -> true
          | uu___ -> false
        then s
        else Prims.strcat "(ignore " (Prims.strcat s ")") in
      let uu___ =
        let uu___1 = let uu___2 = stmts ind e2 in Prims.strcat ind uu___2 in
        Prims.strcat ";\n" uu___1 in
      Prims.strcat s1 uu___
  | uu___ -> term ind e
and case (ind : Prims.string) (br : FStarC_Custard_Syntax.branch) :
  Prims.string=
  let uu___ = br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 = defer_ints Prims.int_zero p in
      (match uu___1 with
       | (uu___2, p1, eqs) ->
           let conds =
             FStarC_List.map
               (fun uu___3 ->
                  match uu___3 with
                  | (x, c) ->
                      let uu___4 = ocaml_local x in
                      let uu___5 =
                        let uu___6 = constant c in Prims.strcat " = " uu___6 in
                      Prims.strcat uu___4 uu___5) eqs in
           let conds1 =
             match g with
             | FStar_Pervasives_Native.None -> conds
             | FStar_Pervasives_Native.Some g1 ->
                 let uu___3 = let uu___4 = term ind g1 in [uu___4] in
                 FStarC_List.op_At conds uu___3 in
           let guard =
             if conds1 = []
             then ""
             else Prims.strcat " when " (FStarC_String.concat " && " conds1) in
           let uu___3 =
             let uu___4 =
               let uu___5 = pattern p1 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 =
                     let uu___9 = term (Prims.strcat ind "  ") b in
                     Prims.strcat uu___9 "\n" in
                   Prims.strcat " -> " uu___8 in
                 Prims.strcat guard uu___7 in
               Prims.strcat uu___5 uu___6 in
             Prims.strcat "| " uu___4 in
           Prims.strcat ind uu___3)
let params (ps : Prims.string Prims.list) : Prims.string=
  match ps with
  | [] -> ""
  | p::[] ->
      let uu___ = let uu___1 = ocaml_var p in Prims.strcat uu___1 " " in
      Prims.strcat "'" uu___
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_List.map
              (fun p -> let uu___4 = ocaml_var p in Prims.strcat "'" uu___4)
              ps in
          FStarC_String.concat ", " uu___3 in
        Prims.strcat uu___2 ") " in
      Prims.strcat "(" uu___1
let print_decl (first : Prims.bool) (d : FStarC_Custard_Syntax.decl) :
  Prims.string FStar_Pervasives_Native.option=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      let uu___ =
        let uu___1 = is_builtin_type t.FStarC_Custard_Syntax.dt_name in
        if uu___1
        then true
        else
          FStarC_Custard_Syntax.has_flag t.FStarC_Custard_Syntax.dt_flags
            FStarC_Custard_Syntax.Realized in
      if uu___
      then FStar_Pervasives_Native.None
      else
        (let hd =
           let uu___1 =
             let uu___2 = params t.FStarC_Custard_Syntax.dt_params in
             let uu___3 = ocaml_type_name t.FStarC_Custard_Syntax.dt_name in
             Prims.strcat uu___2 uu___3 in
           Prims.strcat (if first then "type " else "and ") uu___1 in
         match t.FStarC_Custard_Syntax.dt_body with
         | FStarC_Custard_Syntax.TAbstract -> FStar_Pervasives_Native.Some hd
         | FStarC_Custard_Syntax.TAbbrev c ->
             let uu___1 =
               let uu___2 = let uu___3 = ty c in Prims.strcat " = " uu___3 in
               Prims.strcat hd uu___2 in
             FStar_Pervasives_Native.Some uu___1
         | FStarC_Custard_Syntax.TRecord fs ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStarC_List.map
                         (fun uu___6 ->
                            match uu___6 with
                            | (f, c) ->
                                let uu___7 =
                                  let uu___8 = ocaml_var f in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 = ty c in
                                      Prims.strcat uu___11 ";\n" in
                                    Prims.strcat " : " uu___10 in
                                  Prims.strcat uu___8 uu___9 in
                                Prims.strcat "  " uu___7) fs in
                     FStarC_String.concat "" uu___5 in
                   Prims.strcat uu___4 "}" in
                 Prims.strcat " = {\n" uu___3 in
               Prims.strcat hd uu___2 in
             FStar_Pervasives_Native.Some uu___1
         | FStarC_Custard_Syntax.TVariant cs ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_List.map
                       (fun uu___5 ->
                          match uu___5 with
                          | (c, fs) ->
                              let uu___6 =
                                let uu___7 = ctor_ref c in
                                let uu___8 =
                                  let uu___9 =
                                    match fs with
                                    | [] -> ""
                                    | uu___10 ->
                                        let uu___11 =
                                          let uu___12 =
                                            FStarC_List.map
                                              (fun uu___13 ->
                                                 match uu___13 with
                                                 | (uu___14, t1) -> ty t1) fs in
                                          FStarC_String.concat " * " uu___12 in
                                        Prims.strcat " of " uu___11 in
                                  Prims.strcat uu___9 "\n" in
                                Prims.strcat uu___7 uu___8 in
                              Prims.strcat "  | " uu___6) cs in
                   FStarC_String.concat "" uu___4 in
                 Prims.strcat " =\n" uu___3 in
               Prims.strcat hd uu___2 in
             FStar_Pervasives_Native.Some uu___1)
  | FStarC_Custard_Syntax.DExternal uu___ -> FStar_Pervasives_Native.None
  | FStarC_Custard_Syntax.DExn e ->
      let uu___ =
        let uu___1 =
          let uu___2 = ocaml_ctor_ident e.FStarC_Custard_Syntax.de_name in
          let uu___3 =
            match e.FStarC_Custard_Syntax.de_args with
            | [] -> ""
            | args ->
                let uu___4 =
                  let uu___5 = FStarC_List.map ty args in
                  FStarC_String.concat " * " uu___5 in
                Prims.strcat " of " uu___4 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat "exception " uu___1 in
      FStar_Pervasives_Native.Some uu___
  | FStarC_Custard_Syntax.DLet l ->
      let bs =
        let uu___ =
          FStarC_List.map
            (fun b ->
               let uu___1 =
                 let uu___2 = ocaml_local b.FStarC_Custard_Syntax.b_name in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = ty b.FStarC_Custard_Syntax.b_ty in
                     Prims.strcat uu___5 ")" in
                   Prims.strcat " : " uu___4 in
                 Prims.strcat uu___2 uu___3 in
               Prims.strcat " (" uu___1) l.FStarC_Custard_Syntax.dl_binders in
        FStarC_String.concat "" uu___ in
      let rc =
        let uu___ =
          FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Rec
            l.FStarC_Custard_Syntax.dl_flags in
        if uu___ then "rec " else "" in
      let kw = if first then Prims.strcat "let " rc else "and " in
      let uu___ =
        let uu___1 =
          let uu___2 = ocaml_value_name l.FStarC_Custard_Syntax.dl_name in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = ty l.FStarC_Custard_Syntax.dl_ret in
                let uu___7 =
                  let uu___8 = term "  " l.FStarC_Custard_Syntax.dl_body in
                  Prims.strcat " =\n  " uu___8 in
                Prims.strcat uu___6 uu___7 in
              Prims.strcat " : " uu___5 in
            Prims.strcat bs uu___4 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat kw uu___1 in
      FStar_Pervasives_Native.Some uu___
let build_tables (homes : Prims.string FStarC_SMap.t)
  (p : FStarC_Custard_Syntax.program) : unit=
  let tbl = FStarC_SMap.create (Prims.of_int 50) in
  let quals = FStarC_SMap.create (Prims.of_int 50) in
  let real = FStarC_SMap.create (Prims.of_int 20) in
  let tups = FStarC_SMap.create (Prims.of_int 20) in
  let home = FStarC_SMap.create (Prims.of_int 50) in
  let homes1 =
    let uu___ =
      FStarC_List.collect
        (fun d ->
           let uu___1 = FStarC_Custard_Syntax.imported_home d in
           match uu___1 with
           | FStar_Pervasives_Native.Some m ->
               let uu___2 =
                 let uu___3 =
                   FStarC_Custard_Syntax.string_of_name
                     (FStarC_Custard_Syntax.name_of_decl d) in
                 (uu___3, m) in
               [uu___2]
           | FStar_Pervasives_Native.None -> []) p in
    match uu___ with
    | [] -> homes
    | hs ->
        let homes' = FStarC_SMap.copy homes in
        (FStarC_List.iter
           (fun uu___2 ->
              match uu___2 with
              | (n, m) ->
                  let uu___3 = module_name_of_unit m in
                  FStarC_SMap.add homes' n uu___3) hs;
         homes') in
  FStarC_List.iter
    (fun d ->
       let uu___1 = FStarC_Custard_Syntax.imported_unit d in
       match uu___1 with
       | FStar_Pervasives_Native.Some uu___2 when
           let uu___3 = FStarC_Custard_Syntax.imported_home d in
           match uu___3 with
           | FStar_Pervasives_Native.Some v -> true
           | uu___4 -> false ->
           (match d with
            | FStarC_Custard_Syntax.DExternal e ->
                let uu___3 =
                  FStarC_Custard_Syntax.string_of_name
                    e.FStarC_Custard_Syntax.dx_name in
                let uu___4 =
                  match e.FStarC_Custard_Syntax.dx_target with
                  | FStar_Pervasives_Native.Some t -> t
                  | FStar_Pervasives_Native.None ->
                      realization_of e.FStarC_Custard_Syntax.dx_name in
                FStarC_SMap.add tbl uu___3 uu___4
            | uu___3 -> ())
       | FStar_Pervasives_Native.Some u ->
           let m = module_name_of_unit u in
           (match d with
            | FStarC_Custard_Syntax.DLet l ->
                let uu___2 =
                  FStarC_Custard_Syntax.string_of_name
                    l.FStarC_Custard_Syntax.dl_name in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      ocaml_value_name l.FStarC_Custard_Syntax.dl_name in
                    Prims.strcat "." uu___5 in
                  Prims.strcat m uu___4 in
                FStarC_SMap.add tbl uu___2 uu___3
            | FStarC_Custard_Syntax.DExternal e ->
                let uu___2 =
                  FStarC_Custard_Syntax.string_of_name
                    e.FStarC_Custard_Syntax.dx_name in
                let uu___3 =
                  match e.FStarC_Custard_Syntax.dx_target with
                  | FStar_Pervasives_Native.Some t -> t
                  | FStar_Pervasives_Native.None ->
                      realization_of e.FStarC_Custard_Syntax.dx_name in
                FStarC_SMap.add tbl uu___2 uu___3
            | FStarC_Custard_Syntax.DType t ->
                ((let uu___3 =
                    FStarC_Custard_Syntax.string_of_name
                      t.FStarC_Custard_Syntax.dt_name in
                  FStarC_SMap.add quals uu___3 m);
                 (match t.FStarC_Custard_Syntax.dt_body with
                  | FStarC_Custard_Syntax.TVariant cs ->
                      FStarC_List.iter
                        (fun uu___3 ->
                           match uu___3 with
                           | (cn, uu___4) ->
                               let uu___5 =
                                 FStarC_Custard_Syntax.string_of_name cn in
                               FStarC_SMap.add quals uu___5 m) cs
                  | uu___3 -> ()))
            | FStarC_Custard_Syntax.DExn uu___2 -> ())
       | FStar_Pervasives_Native.None ->
           (match d with
            | FStarC_Custard_Syntax.DExternal e ->
                let uu___2 =
                  FStarC_Custard_Syntax.string_of_name
                    e.FStarC_Custard_Syntax.dx_name in
                let uu___3 =
                  match e.FStarC_Custard_Syntax.dx_target with
                  | FStar_Pervasives_Native.Some t -> t
                  | FStar_Pervasives_Native.None ->
                      realization_of e.FStarC_Custard_Syntax.dx_name in
                FStarC_SMap.add tbl uu___2 uu___3
            | uu___2 -> ())) p;
  FStarC_List.iter
    (fun d ->
       let n = FStarC_Custard_Syntax.name_of_decl d in
       let uu___2 =
         let uu___3 = FStarC_Custard_Syntax.string_of_name n in
         FStarC_SMap.try_find homes1 uu___3 in
       match uu___2 with
       | FStar_Pervasives_Native.None -> ()
       | FStar_Pervasives_Native.Some m ->
           let mark x =
             (let uu___4 = FStarC_Custard_Syntax.string_of_name x in
              FStarC_SMap.add quals uu___4 m);
             (let uu___4 =
                if
                  match x.FStarC_Custard_Syntax.spec with
                  | FStar_Pervasives_Native.None -> true
                  | uu___5 -> false
                then
                  let uu___5 =
                    module_name_of_unit
                      (FStarC_String.concat "." x.FStarC_Custard_Syntax.ns) in
                  uu___5 = m
                else false in
              if uu___4
              then
                let uu___5 = FStarC_Custard_Syntax.string_of_name x in
                FStarC_SMap.add home uu___5 ()
              else ()) in
           (mark n;
            (match d with
             | FStarC_Custard_Syntax.DType t ->
                 (match t.FStarC_Custard_Syntax.dt_body with
                  | FStarC_Custard_Syntax.TVariant cs ->
                      FStarC_List.iter
                        (fun uu___4 ->
                           match uu___4 with | (cn, uu___5) -> mark cn) cs
                  | uu___4 -> ())
             | uu___4 -> ()))) p;
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t when
           FStarC_Custard_Syntax.has_flag t.FStarC_Custard_Syntax.dt_flags
             FStarC_Custard_Syntax.Realized
           ->
           let m =
             FStarC_String.concat "_"
               (t.FStarC_Custard_Syntax.dt_name).FStarC_Custard_Syntax.ns in
           let mark n =
             (let uu___4 = FStarC_Custard_Syntax.string_of_name n in
              FStarC_SMap.add real uu___4 ());
             (let uu___4 = FStarC_Custard_Syntax.string_of_name n in
              FStarC_SMap.add quals uu___4 m) in
           (mark t.FStarC_Custard_Syntax.dt_name;
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TVariant cs ->
                 FStarC_List.iter
                   (fun uu___5 -> match uu___5 with | (cn, uu___6) -> mark cn)
                   cs
             | uu___5 -> ());
            (let uu___5 = is_tuple_type t.FStarC_Custard_Syntax.dt_name in
             if uu___5
             then
               let arity fs =
                 let uu___6 =
                   FStarC_Custard_Syntax.string_of_name
                     t.FStarC_Custard_Syntax.dt_name in
                 FStarC_SMap.add tups uu___6 (FStarC_List.length fs) in
               match t.FStarC_Custard_Syntax.dt_body with
               | FStarC_Custard_Syntax.TRecord fs -> arity fs
               | FStarC_Custard_Syntax.TVariant ((cn, fs)::[]) ->
                   (arity fs;
                    (let uu___7 = FStarC_Custard_Syntax.string_of_name cn in
                     FStarC_SMap.add tups uu___7 (FStarC_List.length fs)))
               | uu___6 -> ()
             else ()))
       | uu___3 -> ()) p;
  (let recs = FStarC_SMap.create (Prims.of_int 100) in
   let labels = FStarC_SMap.create (Prims.of_int 100) in
   FStarC_List.iter
     (fun d ->
        match d with
        | FStarC_Custard_Syntax.DType t ->
            (match t.FStarC_Custard_Syntax.dt_body with
             | FStarC_Custard_Syntax.TRecord fs ->
                 ((let uu___5 =
                     FStarC_Custard_Syntax.string_of_name
                       t.FStarC_Custard_Syntax.dt_name in
                   FStarC_SMap.add recs uu___5
                     (FStarC_List.length t.FStarC_Custard_Syntax.dt_params));
                  FStarC_List.iter
                    (fun uu___5 ->
                       match uu___5 with
                       | (f, uu___6) ->
                           let k =
                             label_key t.FStarC_Custard_Syntax.dt_name f in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = FStarC_SMap.try_find labels k in
                               match uu___9 with
                               | FStar_Pervasives_Native.Some i -> i
                               | FStar_Pervasives_Native.None ->
                                   Prims.int_zero in
                             Prims.int_one + uu___8 in
                           FStarC_SMap.add labels k uu___7) fs)
             | uu___4 -> ())
        | uu___4 -> ()) p;
   FStarC_Effect.op_Colon_Equals externals tbl;
   FStarC_Effect.op_Colon_Equals qualifiers quals;
   FStarC_Effect.op_Colon_Equals realized real;
   FStarC_Effect.op_Colon_Equals tuples tups;
   FStarC_Effect.op_Colon_Equals record_params recs;
   FStarC_Effect.op_Colon_Equals record_labels labels;
   FStarC_Effect.op_Colon_Equals at_home home;
   (let uu___12 = FStarC_SMap.create Prims.int_zero in
    FStarC_Effect.op_Colon_Equals exn_idents uu___12);
   (let exns =
      FStarC_List.collect
        (fun d ->
           match d with
           | FStarC_Custard_Syntax.DExn e when
               if
                 match (e.FStarC_Custard_Syntax.de_name).FStarC_Custard_Syntax.spec
                 with
                 | FStar_Pervasives_Native.None -> true
                 | uu___12 -> false
               then
                 let uu___12 = is_at_home e.FStarC_Custard_Syntax.de_name in
                 Prims.not uu___12
               else false -> [e.FStarC_Custard_Syntax.de_name]
           | uu___12 -> []) p in
    let short n =
      let uu___12 = sanitize n.FStarC_Custard_Syntax.id in
      uppercase_first uu___12 in
    let taken = FStarC_SMap.create (Prims.of_int 50) in
    FStarC_List.iter
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DType t ->
             (match t.FStarC_Custard_Syntax.dt_body with
              | FStarC_Custard_Syntax.TVariant cs ->
                  FStarC_List.iter
                    (fun uu___13 ->
                       match uu___13 with
                       | (cn, uu___14) ->
                           let uu___15 = ocaml_ctor_ident cn in
                           FStarC_SMap.add taken uu___15 ()) cs
              | uu___13 -> ())
         | FStarC_Custard_Syntax.DExn e ->
             let uu___13 =
               let uu___14 =
                 FStarC_List.existsb
                   (fun x ->
                      let uu___15 = FStarC_Custard_Syntax.string_of_name x in
                      let uu___16 =
                        FStarC_Custard_Syntax.string_of_name
                          e.FStarC_Custard_Syntax.de_name in
                      uu___15 = uu___16) exns in
               Prims.not uu___14 in
             if uu___13
             then
               let uu___14 = ocaml_ctor_ident e.FStarC_Custard_Syntax.de_name in
               FStarC_SMap.add taken uu___14 ()
             else ()
         | uu___13 -> ()) p;
    (let counts = FStarC_SMap.create (Prims.of_int 20) in
     FStarC_List.iter
       (fun n ->
          let k = short n in
          let uu___14 =
            let uu___15 =
              let uu___16 = FStarC_SMap.try_find counts k in
              match uu___16 with
              | FStar_Pervasives_Native.Some i -> i
              | FStar_Pervasives_Native.None -> Prims.int_zero in
            Prims.int_one + uu___15 in
          FStarC_SMap.add counts k uu___14) exns;
     (let exn_tbl = FStarC_SMap.create (Prims.of_int 20) in
      FStarC_List.iter
        (fun n ->
           let k = short n in
           let uu___15 =
             let uu___16 =
               let uu___17 =
                 let uu___18 = FStarC_SMap.try_find counts k in
                 uu___18 = (FStar_Pervasives_Native.Some Prims.int_one) in
               if uu___17
               then
                 let uu___18 = FStarC_SMap.try_find taken k in
                 match uu___18 with
                 | FStar_Pervasives_Native.None -> true
                 | uu___19 -> false
               else false in
             if uu___16
             then Prims.not (FStarC_List.mem k predefined_ctors)
             else false in
           if uu___15
           then
             let uu___16 = FStarC_Custard_Syntax.string_of_name n in
             FStarC_SMap.add exn_tbl uu___16 k
           else ()) exns;
      FStarC_Effect.op_Colon_Equals exn_idents exn_tbl))))
let header : Prims.string=
  "(* Generated by F* Custard extraction. Do not edit. *)\n[@@@ocaml.warning \"-3-5-8-11-20-26-27-28-32-33-34-35-37-39-50-57-60-69-70\"]\n"
let group_of (d : FStarC_Custard_Syntax.decl) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind FStarC_Custard_Syntax.uu___is_Rec
      (FStarC_Custard_Syntax.decl_flags d) in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.Rec ns) ->
      let uu___1 = FStarC_List.map FStarC_Custard_Syntax.string_of_name ns in
      FStar_Pervasives_Native.Some uu___1
  | uu___1 -> FStar_Pervasives_Native.None
let print_decls (p : FStarC_Custard_Syntax.program) :
  Prims.string Prims.list=
  let prev = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  FStarC_List.collect
    (fun d ->
       let uu___ =
         let uu___1 = FStarC_Custard_Syntax.imported_unit d in
         match uu___1 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___2 -> false in
       if uu___
       then []
       else
         (let g = group_of d in
          let first =
            if
              match g with
              | FStar_Pervasives_Native.None -> true
              | uu___1 -> false
            then true
            else (let uu___1 = FStarC_Effect.op_Bang prev in g <> uu___1) in
          let uu___1 = print_decl first d in
          match uu___1 with
          | FStar_Pervasives_Native.Some s ->
              (FStarC_Effect.op_Colon_Equals prev g; [s])
          | FStar_Pervasives_Native.None -> [])) p
let entry_calls (p : FStarC_Custard_Syntax.program) :
  Prims.string Prims.list=
  FStarC_List.collect
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l when
           let uu___ =
             FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Entrypoint
               l.FStarC_Custard_Syntax.dl_flags in
           if uu___
           then
             FStarC_List.for_all
               (fun b ->
                  match b.FStarC_Custard_Syntax.b_ty with
                  | FStarC_Custard_Syntax.TUnit -> true
                  | uu___1 -> false) l.FStarC_Custard_Syntax.dl_binders
           else false ->
           let args =
             let uu___ =
               FStarC_List.map (fun uu___1 -> "()")
                 l.FStarC_Custard_Syntax.dl_binders in
             FStarC_String.concat " " uu___ in
           let call =
             let uu___ =
               let uu___1 = ocaml_value_name l.FStarC_Custard_Syntax.dl_name in
               qualify l.FStarC_Custard_Syntax.dl_name uu___1 in
             Prims.strcat uu___ (Prims.strcat " " args) in
           (match l.FStarC_Custard_Syntax.dl_ret with
            | FStarC_Custard_Syntax.TInt sw ->
                let uu___ =
                  let uu___1 =
                    let uu___2 = int_module sw in
                    Prims.strcat uu___2
                      (Prims.strcat ".v (" (Prims.strcat call ")))")) in
                  Prims.strcat "let _ = Stdlib.exit (Z.to_int (" uu___1 in
                [uu___]
            | uu___ -> [Prims.strcat "let _ = " call])
       | uu___ -> []) p
let assemble (ds : Prims.string Prims.list) : Prims.string=
  Prims.strcat header
    (Prims.strcat "\n" (Prims.strcat (FStarC_String.concat "\n\n" ds) "\n"))
let reserve_top (p : FStarC_Custard_Syntax.program) : unit=
  let uu___ =
    FStarC_List.collect
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DLet l ->
             let uu___1 = ocaml_value_name l.FStarC_Custard_Syntax.dl_name in
             [uu___1]
         | FStarC_Custard_Syntax.DExternal e ->
             let uu___1 = ocaml_value_name e.FStarC_Custard_Syntax.dx_name in
             [uu___1]
         | uu___1 -> []) p in
  FStarC_Effect.op_Colon_Equals reserved_top uu___
let reject_target_only_types (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType ty1 ->
           FStarC_List.iter
             (fun f ->
                match f with
                | FStarC_Custard_Syntax.Extern
                    (FStar_Pervasives_Native.Some target, uu___) when
                    let uu___1 =
                      FStarC_Custard_Syntax.template_of_string target in
                    FStarC_Custard_Syntax.is_template uu___1 ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              FStarC_Custard_Syntax.string_of_name
                                ty1.FStarC_Custard_Syntax.dt_name in
                            Prims.strcat uu___5
                              " has a template target, and templates reached the OCaml backend." in
                          Prims.strcat "Custard: the external type " uu___4 in
                        FStarC_Errors_Msg.text uu___3 in
                      [uu___2;
                      FStarC_Errors_Msg.text
                        (Prims.strcat "Its target spelling ["
                           (Prims.strcat target
                              "] has a placeholder for an argument, so two instantiations of it are two different target types; OCaml has no such construction.  Section 69 is a C-backend feature (--custard_backend C)."));
                      FStarC_Errors_Msg.text
                        "The unparameterized form still works everywhere: a [@@custard_extern] target with no [{0}] placeholder names one target type, and its arguments are dropped."] in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___1)
                | FStarC_Custard_Syntax.CReference ->
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          let uu___3 =
                            let uu___4 =
                              FStarC_Custard_Syntax.string_of_name
                                ty1.FStarC_Custard_Syntax.dt_name in
                            Prims.strcat uu___4
                              " is [@@custard_c_reference], and reference bindings reached the OCaml backend." in
                          Prims.strcat "Custard: the external type " uu___3 in
                        FStarC_Errors_Msg.text uu___2 in
                      [uu___1;
                      FStarC_Errors_Msg.text
                        "The attribute says that values of the type are handles, so a binding of one has to alias rather than copy -- which is C++ [T &x = ...], and OCaml has no way to spell it.  Emitting a copy instead would compile and be wrong, which is the exact failure the attribute exists to prevent.";
                      FStarC_Errors_Msg.text
                        "Section 70.2 is a C-backend feature (--custard_backend C)."] in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Error_CustardBadReference ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___)
                | uu___ -> ()) ty1.FStarC_Custard_Syntax.dt_flags
       | uu___ -> ()) p
let print_program (p : FStarC_Custard_Syntax.program) : Prims.string=
  reject_target_only_types p;
  (let uu___2 = FStarC_SMap.create Prims.int_zero in build_tables uu___2 p);
  FStarC_Effect.op_Colon_Equals current_module FStar_Pervasives_Native.None;
  reserve_top p;
  (let uu___4 =
     let uu___5 = print_decls p in
     let uu___6 = entry_calls p in FStarC_List.op_At uu___5 uu___6 in
   assemble uu___4)
let print_split
  (files : (Prims.string * FStarC_Custard_Syntax.program) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  (let uu___1 = FStarC_List.collect FStar_Pervasives_Native.snd files in
   reject_target_only_types uu___1);
  (let homes = FStarC_SMap.create (Prims.of_int 100) in
   FStarC_List.iter
     (fun uu___2 ->
        match uu___2 with
        | (m, ds) ->
            let m1 = module_name_of_unit m in
            FStarC_List.iter
              (fun d ->
                 let uu___3 =
                   FStarC_Custard_Syntax.string_of_name
                     (FStarC_Custard_Syntax.name_of_decl d) in
                 FStarC_SMap.add homes uu___3 m1) ds) files;
   FStarC_Custard_Prof.timed "p.tables"
     (fun uu___3 ->
        let uu___4 = FStarC_List.collect FStar_Pervasives_Native.snd files in
        build_tables homes uu___4);
   (let rendered =
      FStarC_List.map
        (fun uu___3 ->
           match uu___3 with
           | (m, ds) ->
               let m1 = module_name_of_unit m in
               (FStarC_Effect.op_Colon_Equals current_module
                  (FStar_Pervasives_Native.Some m1);
                reserve_top ds;
                (let r =
                   let uu___6 =
                     FStarC_Custard_Prof.timed "p.decls"
                       (fun uu___7 -> print_decls ds) in
                   (m1, uu___6) in
                 FStarC_Effect.op_Colon_Equals current_module
                   FStar_Pervasives_Native.None;
                 r))) files in
    let rendered1 =
      FStarC_List.filter
        (fun uu___3 ->
           match uu___3 with
           | (uu___4, ds) ->
               (match ds with | hd::tl -> true | uu___5 -> false)) rendered in
    let n = FStarC_List.length rendered1 in
    let last =
      if n = Prims.int_zero
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.fst (FStarC_List.last rendered1)) in
    FStarC_Effect.op_Colon_Equals current_module last;
    (let calls =
       let uu___4 = FStarC_List.collect FStar_Pervasives_Native.snd files in
       entry_calls uu___4 in
     FStarC_Effect.op_Colon_Equals current_module
       FStar_Pervasives_Native.None;
     FStarC_List.mapi
       (fun i uu___5 ->
          match uu___5 with
          | (m, ds) ->
              let uu___6 =
                FStarC_Custard_Prof.timed "p.render"
                  (fun uu___7 ->
                     assemble
                       (if i = (n - Prims.int_one)
                        then FStarC_List.op_At ds calls
                        else ds)) in
              (m, uu___6)) rendered1)))
