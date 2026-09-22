open Prims
let text : Prims.string -> FStar_Pprint.document= FStarC_Errors_Msg.text
let spaces (n : Prims.int) : Prims.string=
  if n <= Prims.int_zero then "" else FStarC_String.make n 32
let col_after (c : Prims.int) (s : Prims.string) : Prims.int=
  let n = FStarC_String.length s in
  let rec go i =
    if i <= Prims.int_zero
    then c + n
    else
      (let uu___ =
         let uu___1 = FStarC_String.get s (i - Prims.int_one) in uu___1 = 10 in
       if uu___ then n - i else go (i - Prims.int_one)) in
  go n
let after (ind : Prims.string) (s : Prims.string) : Prims.string=
  let uu___ = col_after (FStarC_String.length ind) s in spaces uu___
let rec join_at_aux :
  'a .
    Prims.string Prims.list ->
      Prims.int ->
        Prims.string ->
          (Prims.string -> 'a -> Prims.string) ->
            'a Prims.list -> Prims.string Prims.list
  =
  fun acc col sep f xs ->
    match xs with
    | [] -> acc
    | x::[] ->
        let uu___ = let uu___1 = spaces col in f uu___1 x in uu___ :: acc
    | x::xs1 ->
        let s = let uu___ = spaces col in f uu___ x in
        let col1 = let uu___ = col_after col s in col_after uu___ sep in
        join_at_aux (sep :: s :: acc) col1 sep f xs1
let join_at (ind : Prims.string) (pre : Prims.string) (sep : Prims.string)
  (f : Prims.string -> 'a -> Prims.string) (xs : 'a Prims.list) :
  Prims.string=
  let col = col_after (FStarC_String.length ind) pre in
  let uu___ =
    let uu___1 = join_at_aux [pre] col sep f xs in FStarC_List.rev uu___1 in
  FStarC_String.concat "" uu___
let line_width : Prims.int= Prims.of_int 80
let externals : Prims.string FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let external_target (n : FStarC_Custard_Syntax.name) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang externals in
  let uu___1 = FStarC_Custard_Syntax.string_of_name n in
  FStarC_SMap.try_find uu___ uu___1
let tuples : Prims.int FStarC_SMap.t FStarC_Effect.ref=
  let uu___ = FStarC_SMap.create Prims.int_zero in FStarC_Effect.mk_ref uu___
let nullary : unit FStarC_SMap.t FStarC_Effect.ref=
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
let is_nullary_ctor (n : FStarC_Custard_Syntax.name) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang nullary in
    let uu___2 = FStarC_Custard_Syntax.string_of_name n in
    FStarC_SMap.try_find uu___1 uu___2 in
  match uu___ with | FStar_Pervasives_Native.Some v -> true | uu___1 -> false
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
let fsharp_keywords : Prims.string Prims.list=
  ["abstract";
  "and";
  "as";
  "assert";
  "base";
  "begin";
  "class";
  "default";
  "delegate";
  "do";
  "done";
  "downcast";
  "downto";
  "elif";
  "else";
  "end";
  "exception";
  "extern";
  "false";
  "finally";
  "fixed";
  "for";
  "fun";
  "function";
  "global";
  "if";
  "in";
  "inherit";
  "inline";
  "interface";
  "internal";
  "lazy";
  "let";
  "match";
  "member";
  "module";
  "mutable";
  "namespace";
  "new";
  "not";
  "null";
  "of";
  "open";
  "or";
  "override";
  "private";
  "public";
  "rec";
  "return";
  "select";
  "static";
  "struct";
  "then";
  "to";
  "true";
  "try";
  "type";
  "upcast";
  "use";
  "val";
  "void";
  "when";
  "while";
  "with";
  "yield";
  "atomic";
  "break";
  "checked";
  "component";
  "const";
  "constraint";
  "constructor";
  "continue";
  "eager";
  "event";
  "external";
  "functor";
  "include";
  "method";
  "mixin";
  "object";
  "parallel";
  "process";
  "protected";
  "pure";
  "sealed";
  "tailcall";
  "trait";
  "virtual";
  "asr";
  "land";
  "lor";
  "lsl";
  "lsr";
  "lxor";
  "mod";
  "sig"]
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
  let uu___ = FStarC_List.existsb (fun k -> k = s) fsharp_keywords in
  if uu___ then Prims.strcat "``" (Prims.strcat s "``") else s
let fsharp_value_name (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Custard_Syntax.mangled_name n in sanitize uu___2 in
    lowercase_first uu___1 in
  escape_keyword uu___
let fsharp_type_name (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Custard_Syntax.mangled_name n in sanitize uu___2 in
    lowercase_first uu___1 in
  escape_keyword uu___
let fsharp_ctor_ident (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.mangled_name n in sanitize uu___1 in
  uppercase_first uu___
let module_name_of_unit (u : Prims.string) : Prims.string=
  let uu___ = sanitize u in uppercase_first uu___
let fsharp_var (x : Prims.string) : Prims.string=
  let uu___ = let uu___1 = sanitize x in lowercase_first uu___1 in
  escape_keyword uu___
let fsharp_tyvar (x : Prims.string) : Prims.string=
  let s = let uu___ = sanitize x in lowercase_first uu___ in
  let s1 =
    let uu___ =
      FStarC_List.map
        (fun c ->
           match FStarC_Util.int_of_char c with
           | uu___1 when uu___1 = (Prims.of_int 39) -> "_"
           | uu___1 when uu___1 = (Prims.of_int 95) -> "__"
           | uu___1 -> FStarC_Util.string_of_char c)
        (FStarC_String.list_of_string s) in
    FStarC_String.concat "" uu___ in
  let uu___ =
    let uu___1 = FStarC_List.existsb (fun k -> k = s1) fsharp_keywords in
    if uu___1 then Prims.strcat s1 "_q" else s1 in
  Prims.strcat "'" uu___
let reserved_top : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let fsharp_local (x : Prims.string) : Prims.string=
  let s = fsharp_var x in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang reserved_top in
    FStarC_List.existsb (fun k -> k = s) uu___1 in
  if uu___ then Prims.strcat s "_" else s
let int_type (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  : Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      (match w with
       | FStarC_Custard_Syntax.WSizet -> "uint64"
       | FStarC_Custard_Syntax.W128 ->
           (match s with
            | FStarC_Const.Unsigned -> "System.UInt128"
            | FStarC_Const.Signed -> "System.Int128")
       | uu___1 ->
           Prims.strcat
             (match s with
              | FStarC_Const.Unsigned -> "uint"
              | FStarC_Const.Signed -> "int")
             (match w with
              | FStarC_Custard_Syntax.W8 -> "8"
              | FStarC_Custard_Syntax.W16 -> "16"
              | FStarC_Custard_Syntax.W32 -> "32"
              | FStarC_Custard_Syntax.W64 -> "64"
              | FStarC_Custard_Syntax.W128 -> "64"
              | FStarC_Custard_Syntax.WSizet -> "64"))
let int_suffix
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      (match w with
       | FStarC_Custard_Syntax.WSizet -> "UL"
       | FStarC_Custard_Syntax.W8 ->
           (match s with
            | FStarC_Const.Unsigned -> "uy"
            | FStarC_Const.Signed -> "y")
       | FStarC_Custard_Syntax.W16 ->
           (match s with
            | FStarC_Const.Unsigned -> "us"
            | FStarC_Const.Signed -> "s")
       | FStarC_Custard_Syntax.W32 ->
           (match s with
            | FStarC_Const.Unsigned -> "u"
            | FStarC_Const.Signed -> "")
       | FStarC_Custard_Syntax.W64 ->
           (match s with
            | FStarC_Const.Unsigned -> "UL"
            | FStarC_Const.Signed -> "L")
       | FStarC_Custard_Syntax.W128 -> "")
let is_w128 (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth)) :
  Prims.bool=
  match FStar_Pervasives_Native.snd sw with
  | FStarC_Custard_Syntax.W128 -> true
  | uu___ -> false
let reject_fwidth (fw : FStarC_Custard_Syntax.fwidth) : unit=
  if
    (match fw with | FStarC_Custard_Syntax.Float64 -> true | uu___ -> false)
      ||
      (match fw with | FStarC_Custard_Syntax.Float32 -> true | uu___ -> false)
  then ()
  else
    (let format =
       match fw with
       | FStarC_Custard_Syntax.Float32 -> "binary32"
       | FStarC_Custard_Syntax.Float64 -> "binary64"
       | FStarC_Custard_Syntax.Float16 -> "binary16"
       | FStarC_Custard_Syntax.BFloat16 -> "bfloat16" in
     FStarC_Errors.raise_error0
       FStarC_Errors_Codes.Error_CustardNoCRepresentation ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic
          [text
             (Prims.strcat "Custard: "
                (Prims.strcat format " has no F# representation."));
          text
            "F# has float (binary64) and float32 (binary32) and nothing narrower that arithmetic is defined on, so such a program would compute at a width it did not ask for (sections 38 and 122.5).";
          text
            "Use FStar.Float32 or FStar.Float64, or extract with --custard_backend C."]))
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
  | "Prims.int" -> FStar_Pervasives_Native.Some "bigint"
  | "Prims.exn" -> FStar_Pervasives_Native.Some "exn"
  | "Prims.list" -> FStar_Pervasives_Native.Some "list"
  | "FStar.Pervasives.Native.option" -> FStar_Pervasives_Native.Some "option"
  | uu___ -> FStar_Pervasives_Native.None
let is_builtin_type (n : FStarC_Custard_Syntax.name) : Prims.bool=
  let uu___ = builtin_type n in
  match uu___ with | FStar_Pervasives_Native.Some v -> true | uu___1 -> false
let rec ty (t : FStarC_Custard_Syntax.cty) : Prims.string=
  match t with
  | FStarC_Custard_Syntax.TUnit -> "unit"
  | FStarC_Custard_Syntax.TExn -> "exn"
  | FStarC_Custard_Syntax.TAny -> "obj"
  | FStarC_Custard_Syntax.TVar x -> fsharp_tyvar x
  | FStarC_Custard_Syntax.TInt sw -> int_type sw
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float64) -> "float"
  | FStarC_Custard_Syntax.TFloat (FStarC_Custard_Syntax.Float32) -> "float32"
  | FStarC_Custard_Syntax.TFloat fw -> (reject_fwidth fw; "float")
  | FStarC_Custard_Syntax.TArrow uu___ ->
      let rec split t1 =
        match t1 with
        | FStarC_Custard_Syntax.TArrow (a, uu___1, b) ->
            let uu___2 = split b in
            (match uu___2 with | (args, r) -> ((a :: args), r))
        | uu___1 -> ([], t1) in
      let uu___1 = split t in
      (match uu___1 with
       | (args, ret) ->
           let kept =
             FStarC_List.filter
               (fun a ->
                  Prims.not
                    (match a with
                     | FStarC_Custard_Syntax.TUnit -> true
                     | uu___2 -> false)) args in
           let kept1 =
             if match kept with | [] -> true | uu___2 -> false
             then [FStarC_Custard_Syntax.TUnit]
             else kept in
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_List.map ty kept1 in
               FStarC_String.concat " -> " uu___4 in
             let uu___4 =
               let uu___5 = let uu___6 = ty ret in Prims.strcat uu___6 ")" in
               Prims.strcat " -> " uu___5 in
             Prims.strcat uu___3 uu___4 in
           Prims.strcat "(" uu___2)
  | FStarC_Custard_Syntax.TTuple ts ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map ty ts in
          FStarC_String.concat " * " uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TBuf t1 ->
      let uu___ = let uu___1 = ty t1 in Prims.strcat uu___1 ")[]" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TRef t1 ->
      let uu___ = let uu___1 = ty t1 in Prims.strcat uu___1 " ref)" in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.TInline uu___ ->
      FStarC_Effect.failwith
        "Custard: an inline-field marker reached the F# backend"
  | FStarC_Custard_Syntax.TConst uu___ ->
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardBadTemplateArg ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic
           [text
              "Custard: an external type with a template target reached the F# backend.";
           text
             "[wmma::fragment<matrix_a, 16, 16, 16, half, row_major>] is one type and [wmma::fragment<matrix_b, ...>] another; F# has no such construction, so section 69 is a C-backend feature (--custard_backend C).";
           text
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
       | FStar_Pervasives_Native.None -> fsharp_type_name n)
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let hd =
        let uu___ = builtin_type n in
        match uu___ with
        | FStar_Pervasives_Native.Some s -> s
        | FStar_Pervasives_Native.None -> fsharp_type_name n in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_List.map ty args in
            FStarC_String.concat ", " uu___3 in
          Prims.strcat uu___2 ">" in
        Prims.strcat "<" uu___1 in
      Prims.strcat hd uu___
let rec erased_pun (a : FStarC_Custard_Syntax.cty)
  (b : FStarC_Custard_Syntax.cty) : Prims.bool=
  match (a, b) with
  | (FStarC_Custard_Syntax.TApp (n1, a1), FStarC_Custard_Syntax.TApp
     (n2, a2)) ->
      ((match a1 with | hd::tl -> true | uu___ -> false) ||
         (match a2 with | hd::tl -> true | uu___ -> false))
        && (Prims.not ((n1 = n2) && (a1 = a2)))
  | (FStarC_Custard_Syntax.TBuf t1, FStarC_Custard_Syntax.TBuf t2) ->
      Prims.not (t1 = t2)
  | (FStarC_Custard_Syntax.TRef t1, FStarC_Custard_Syntax.TRef t2) ->
      Prims.not (t1 = t2)
  | (FStarC_Custard_Syntax.TBuf t1, FStarC_Custard_Syntax.TRef t2) ->
      erased_pun t1 t2
  | (FStarC_Custard_Syntax.TRef t1, FStarC_Custard_Syntax.TBuf t2) ->
      erased_pun t1 t2
  | uu___ -> false
let reject_coercion (a : FStarC_Custard_Syntax.cty)
  (b : FStarC_Custard_Syntax.cty) : Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = ty a in
          let uu___5 =
            let uu___6 =
              let uu___7 = ty b in
              Prims.strcat uu___7 ", which .NET cannot express." in
            Prims.strcat " to " uu___6 in
          Prims.strcat uu___4 uu___5 in
        Prims.strcat "Custard: this value changes representation from "
          uu___3 in
      text uu___2 in
    [uu___1;
    text
      "The OCaml backend writes such a change as Obj.magic, which is nothing at run time because every OCaml value has the same shape.  .NET types are not uniform: an unbox is a checked cast, and sized<uint32> is not sized<obj> however the two are laid out (section 122.6.2).";
    text
      "The change is under a type constructor rather than at the top of the type, which is where an erased field can be.  Extract this program with --custard_backend OCaml, or give the declaration a type whose erased part is a field rather than a parameter."] in
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardNoFSharpRealization ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let escape (s : Prims.string) : Prims.string=
  let hexd i =
    let d =
      ["0";
      "1";
      "2";
      "3";
      "4";
      "5";
      "6";
      "7";
      "8";
      "9";
      "a";
      "b";
      "c";
      "d";
      "e";
      "f"] in
    FStarC_List.nth d i in
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
          Prims.strcat "\\u00"
            (Prims.strcat
               (hexd ((mod) (i / (Prims.of_int 16)) (Prims.of_int 16)))
               (hexd ((mod) i (Prims.of_int 16))))
        else FStarC_Util.string_of_char c1 in
  let uu___ = FStarC_List.map esc (FStarC_String.list_of_string s) in
  FStarC_String.concat "" uu___
let int128_literal
  (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (v : Prims.int) (b : FStar_IntegerLiteral.int_base) : Prims.string=
  let uu___ =
    let uu___1 = int_type sw in
    Prims.strcat uu___1
      (Prims.strcat ".Parse \""
         (Prims.strcat
            (FStarC_Custard_Syntax.int_lit_to_string v
               FStar_IntegerLiteral.Dec) "\")")) in
  Prims.strcat "(" uu___
let constant (c : FStarC_Custard_Syntax.constant) : Prims.string=
  match c with
  | FStarC_Custard_Syntax.CUnit -> "()"
  | FStarC_Custard_Syntax.CBool b -> if b then "true" else "false"
  | FStarC_Custard_Syntax.CFloat (FStarC_Custard_Syntax.FLNan, fw) ->
      (reject_fwidth fw;
       if
         (match fw with
          | FStarC_Custard_Syntax.Float32 -> true
          | uu___1 -> false)
       then "(nanf)"
       else "(nan)")
  | FStarC_Custard_Syntax.CFloat (FStarC_Custard_Syntax.FLInf neg, fw) ->
      (reject_fwidth fw;
       Prims.strcat (if neg then "(-" else "(")
         (Prims.strcat
            (if
               match fw with
               | FStarC_Custard_Syntax.Float32 -> true
               | uu___1 -> false
             then "infinityf"
             else "infinity") ")"))
  | FStarC_Custard_Syntax.CFloat (v, fw) ->
      (reject_fwidth fw;
       Prims.strcat "("
         (Prims.strcat (FStarC_Custard_Syntax.float_lit_to_string v)
            (Prims.strcat
               (if
                  match fw with
                  | FStarC_Custard_Syntax.Float32 -> true
                  | uu___1 -> false
                then "f"
                else "") ")")))
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.None) ->
      Prims.strcat "("
        (Prims.strcat
           (FStarC_Custard_Syntax.int_lit_to_string v
              FStar_IntegerLiteral.Dec) "I)")
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.Some sw) when
      is_w128 sw -> int128_literal sw v b
  | FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.Some sw) ->
      let uu___ =
        let uu___1 = let uu___2 = int_suffix sw in Prims.strcat uu___2 ")" in
        Prims.strcat (FStarC_Custard_Syntax.int_lit_to_string v b) uu___1 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.CChar c1 ->
      FStarC_Class_Show.show FStarC_Class_Show.showable_int
        (FStarC_Util.int_of_char c1)
  | FStarC_Custard_Syntax.CString s ->
      let uu___ = let uu___1 = escape s in Prims.strcat uu___1 "\"" in
      Prims.strcat "\"" uu___
let binop (at_width : Prims.bool) (o : FStarC_Custard_Syntax.op) :
  Prims.string FStar_Pervasives_Native.option=
  match o with
  | FStarC_Custard_Syntax.Add -> FStar_Pervasives_Native.Some "+"
  | FStarC_Custard_Syntax.AddW -> FStar_Pervasives_Native.Some "+"
  | FStarC_Custard_Syntax.Sub -> FStar_Pervasives_Native.Some "-"
  | FStarC_Custard_Syntax.SubW -> FStar_Pervasives_Native.Some "-"
  | FStarC_Custard_Syntax.Mult -> FStar_Pervasives_Native.Some "*"
  | FStarC_Custard_Syntax.MultW -> FStar_Pervasives_Native.Some "*"
  | FStarC_Custard_Syntax.Div -> FStar_Pervasives_Native.Some "/"
  | FStarC_Custard_Syntax.DivW -> FStar_Pervasives_Native.Some "/"
  | FStarC_Custard_Syntax.Mod -> FStar_Pervasives_Native.Some "%"
  | FStarC_Custard_Syntax.Eq -> FStar_Pervasives_Native.Some "="
  | FStarC_Custard_Syntax.Neq -> FStar_Pervasives_Native.Some "<>"
  | FStarC_Custard_Syntax.Lt -> FStar_Pervasives_Native.Some "<"
  | FStarC_Custard_Syntax.Lte -> FStar_Pervasives_Native.Some "<="
  | FStarC_Custard_Syntax.Gt -> FStar_Pervasives_Native.Some ">"
  | FStarC_Custard_Syntax.Gte -> FStar_Pervasives_Native.Some ">="
  | FStarC_Custard_Syntax.BOr -> FStar_Pervasives_Native.Some "|||"
  | FStarC_Custard_Syntax.BAnd -> FStar_Pervasives_Native.Some "&&&"
  | FStarC_Custard_Syntax.BXor -> FStar_Pervasives_Native.Some "^^^"
  | FStarC_Custard_Syntax.And ->
      FStar_Pervasives_Native.Some (if at_width then "&&&" else "&&")
  | FStarC_Custard_Syntax.Or ->
      FStar_Pervasives_Native.Some (if at_width then "|||" else "||")
  | uu___ -> FStar_Pervasives_Native.None
let unop (at_width : Prims.bool) (o : FStarC_Custard_Syntax.op) :
  Prims.string FStar_Pervasives_Native.option=
  match o with
  | FStarC_Custard_Syntax.BNot -> FStar_Pervasives_Native.Some "~~~"
  | FStarC_Custard_Syntax.Not ->
      FStar_Pervasives_Native.Some (if at_width then "~~~" else "not")
  | uu___ -> FStar_Pervasives_Native.None
let w128_unop (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  (o : FStarC_Custard_Syntax.op) :
  Prims.string FStar_Pervasives_Native.option=
  if Prims.not (is_w128 sw)
  then FStar_Pervasives_Native.None
  else
    (match o with
     | FStarC_Custard_Syntax.BNot ->
         FStar_Pervasives_Native.Some
           (Prims.strcat "FStarCustard."
              (if
                 match FStar_Pervasives_Native.fst sw with
                 | FStarC_Const.Unsigned -> true
                 | uu___ -> false
               then "notU128"
               else "notI128"))
     | FStarC_Custard_Syntax.Not ->
         FStar_Pervasives_Native.Some
           (Prims.strcat "FStarCustard."
              (if
                 match FStar_Pervasives_Native.fst sw with
                 | FStarC_Const.Unsigned -> true
                 | uu___ -> false
               then "notU128"
               else "notI128"))
     | uu___ -> FStar_Pervasives_Native.None)
let is_shift (o : FStarC_Custard_Syntax.op) : Prims.bool=
  (match o with | FStarC_Custard_Syntax.BShiftL -> true | uu___ -> false) ||
    (match o with | FStarC_Custard_Syntax.BShiftR -> true | uu___ -> false)
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
let int_conv (sw : (FStarC_Const.signedness * FStarC_Custard_Syntax.iwidth))
  : Prims.string=
  let uu___ = sw in
  match uu___ with
  | (s, w) ->
      (match w with
       | FStarC_Custard_Syntax.WSizet -> "uint64"
       | FStarC_Custard_Syntax.W128 ->
           (match s with
            | FStarC_Const.Unsigned -> "FStarCustard.toU128"
            | FStarC_Const.Signed -> "FStarCustard.toI128")
       | uu___1 -> int_type sw)
let qualified_label (n : FStarC_Custard_Syntax.name) (f : Prims.string) :
  Prims.string=
  let uu___ = is_builtin_type n in
  if uu___
  then fsharp_var f
  else
    (let uu___1 = fsharp_type_name n in
     let uu___2 = let uu___3 = fsharp_var f in Prims.strcat "." uu___3 in
     Prims.strcat uu___1 uu___2)
let ascribe_record (n : FStarC_Custard_Syntax.name) (f : Prims.string)
  (s : Prims.string) : Prims.string=
  let uu___ = let uu___1 = ambiguous_label n f in Prims.not uu___1 in
  if uu___
  then s
  else
    (let uu___1 =
       let uu___2 = FStarC_Effect.op_Bang record_params in
       let uu___3 = FStarC_Custard_Syntax.string_of_name n in
       FStarC_SMap.try_find uu___2 uu___3 in
     match uu___1 with
     | FStar_Pervasives_Native.None -> s
     | FStar_Pervasives_Native.Some k ->
         let rec wilds i =
           if i <= Prims.int_zero
           then []
           else (let uu___2 = wilds (i - Prims.int_one) in "_" :: uu___2) in
         let args =
           if k = Prims.int_zero
           then ""
           else
             (let uu___2 =
                let uu___3 =
                  let uu___4 = wilds k in FStarC_String.concat ", " uu___4 in
                Prims.strcat uu___3 ">" in
              Prims.strcat "<" uu___2) in
         let uu___2 =
           let uu___3 =
             let uu___4 = fsharp_type_name n in Prims.strcat uu___4 args in
           Prims.strcat " : " uu___3 in
         Prims.strcat s uu___2)
let deferred_const (c : FStarC_Custard_Syntax.constant) : Prims.bool=
  match c with
  | FStarC_Custard_Syntax.CInt (uu___, uu___1, FStar_Pervasives_Native.None)
      -> true
  | FStarC_Custard_Syntax.CInt
      (uu___, uu___1, FStar_Pervasives_Native.Some sw) -> is_w128 sw
  | uu___ -> false
let rec defer_ints (n : Prims.int) (p : FStarC_Custard_Syntax.pat) :
  (Prims.int * FStarC_Custard_Syntax.pat * (Prims.string *
    FStarC_Custard_Syntax.constant) Prims.list)=
  match p with
  | FStarC_Custard_Syntax.PConst c when deferred_const c ->
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
let rec pat_scalar_ty (p : FStarC_Custard_Syntax.pat) :
  Prims.string FStar_Pervasives_Native.option=
  match p with
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CUnit) ->
      FStar_Pervasives_Native.Some "unit"
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CBool uu___) ->
      FStar_Pervasives_Native.Some "bool"
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CChar uu___) ->
      FStar_Pervasives_Native.Some "char"
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CString uu___) ->
      FStar_Pervasives_Native.Some "string"
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CFloat (uu___, fw))
      ->
      (reject_fwidth fw;
       FStar_Pervasives_Native.Some
         (if
            (match fw with
             | FStarC_Custard_Syntax.Float32 -> true
             | uu___2 -> false)
          then "float32"
          else "float"))
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CInt
      (uu___, uu___1, FStar_Pervasives_Native.None)) ->
      FStar_Pervasives_Native.Some "bigint"
  | FStarC_Custard_Syntax.PConst (FStarC_Custard_Syntax.CInt
      (uu___, uu___1, FStar_Pervasives_Native.Some sw)) ->
      let uu___2 = int_type sw in FStar_Pervasives_Native.Some uu___2
  | FStarC_Custard_Syntax.POr ps -> FStarC_List.tryPick pat_scalar_ty ps
  | uu___ -> FStar_Pervasives_Native.None
let rec pattern (p : FStarC_Custard_Syntax.pat) : Prims.string=
  match p with
  | FStarC_Custard_Syntax.PWild -> "_"
  | FStarC_Custard_Syntax.PVar x -> fsharp_local x
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
                       then qualified_label n f
                       else fsharp_var f in
                     let uu___5 =
                       let uu___6 = pattern p1 in Prims.strcat " = " uu___6 in
                     Prims.strcat uu___4 uu___5) fs in
          FStarC_String.concat "; " uu___2 in
        Prims.strcat uu___1 " }" in
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
  | FStar_Pervasives_Native.None -> fsharp_ctor_ident n
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
let rec term (ind : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst c -> constant c
  | FStarC_Custard_Syntax.EVar x -> fsharp_local x
  | FStarC_Custard_Syntax.EQual (n, uu___) ->
      let uu___1 = external_target n in
      (match uu___1 with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> fsharp_value_name n)
  | FStarC_Custard_Syntax.ECtor (n, []) -> ctor_ref n
  | FStarC_Custard_Syntax.ECtor (n, a::b::[]) when
      let uu___ = builtin_ctor n in
      uu___ = (FStar_Pervasives_Native.Some "::") ->
      let uu___ = join_at ind "(" " :: " term [a; b] in
      Prims.strcat uu___ ")"
  | FStarC_Custard_Syntax.ECtor (n, args) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let uu___ = join_at ind "(" ", " term args in Prims.strcat uu___ ")"
  | FStarC_Custard_Syntax.ECtor (n, args) ->
      let uu___ =
        let uu___1 =
          let uu___2 = let uu___3 = ctor_ref n in Prims.strcat uu___3 " (" in
          Prims.strcat "(" uu___2 in
        join_at ind uu___1 ", " term args in
      Prims.strcat uu___ "))"
  | FStarC_Custard_Syntax.ETuple es ->
      let uu___ = join_at ind "(" ", " term es in Prims.strcat uu___ ")"
  | FStarC_Custard_Syntax.EApp (hd, args) ->
      let kept =
        FStarC_List.filter
          (fun a ->
             Prims.not
               (match a.FStarC_Custard_Syntax.ty with
                | FStarC_Custard_Syntax.TUnit -> true
                | uu___ -> false)) args in
      let kept1 =
        if match kept with | [] -> true | uu___ -> false then args else kept in
      let uu___ = join_at ind "(" " " term (hd :: kept1) in
      Prims.strcat uu___ ")"
  | FStarC_Custard_Syntax.EFun (bs, body) ->
      let pre =
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_List.map
                (fun b ->
                   let uu___3 =
                     let uu___4 = fsharp_local b.FStarC_Custard_Syntax.b_name in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = ty b.FStarC_Custard_Syntax.b_ty in
                         Prims.strcat uu___7 ")" in
                       Prims.strcat " : " uu___6 in
                     Prims.strcat uu___4 uu___5 in
                   Prims.strcat "(" uu___3) bs in
            FStarC_String.concat " " uu___2 in
          Prims.strcat uu___1 " -> " in
        Prims.strcat "(fun " uu___ in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre in term uu___2 body in
        Prims.strcat uu___1 ")" in
      Prims.strcat pre uu___
  | FStarC_Custard_Syntax.ELet uu___ ->
      let uu___1 =
        let uu___2 = stmts (Prims.strcat ind " ") e in
        Prims.strcat uu___2 ")" in
      Prims.strcat "(" uu___1
  | FStarC_Custard_Syntax.ESeq uu___ ->
      let uu___1 =
        let uu___2 = stmts (Prims.strcat ind " ") e in
        Prims.strcat uu___2 ")" in
      Prims.strcat "(" uu___1
  | FStarC_Custard_Syntax.EIf (c, t, f) ->
      let pre = "(if " in
      let pre1 =
        let uu___ =
          let uu___1 = let uu___2 = after ind pre in term uu___2 c in
          Prims.strcat uu___1 " then " in
        Prims.strcat pre uu___ in
      let pre2 =
        let uu___ =
          let uu___1 = let uu___2 = after ind pre1 in term uu___2 t in
          Prims.strcat uu___1 " else " in
        Prims.strcat pre1 uu___ in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre2 in term uu___2 f in
        Prims.strcat uu___1 ")" in
      Prims.strcat pre2 uu___
  | FStarC_Custard_Syntax.EMatch (scrut, brs) ->
      let ub =
        if
          match scrut.FStarC_Custard_Syntax.ty with
          | FStarC_Custard_Syntax.TAny -> true
          | uu___ -> false
        then
          FStarC_List.tryPick
            (fun uu___ ->
               match uu___ with | (p, uu___1, uu___2) -> pat_scalar_ty p) brs
        else FStar_Pervasives_Native.None in
      let pre =
        Prims.strcat "(match "
          (match ub with
           | FStar_Pervasives_Native.Some t ->
               Prims.strcat "(unbox<" (Prims.strcat t "> ")
           | FStar_Pervasives_Native.None -> "") in
      let hd =
        let uu___ =
          let uu___1 = let uu___2 = after ind pre in term uu___2 scrut in
          Prims.strcat uu___1
            (Prims.strcat
               (if
                  match ub with
                  | FStar_Pervasives_Native.Some v -> true
                  | uu___2 -> false
                then ")"
                else "") " with\n") in
        Prims.strcat pre uu___ in
      let ind' = Prims.strcat ind " " in
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (case ind') brs in
          FStarC_String.concat "\n" uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat hd uu___
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
                   | (f, e1) ->
                       let uu___5 = term (Prims.strcat ind " ") e1 in
                       (f, uu___5)) fs in
            by_position k "(Unchecked.defaultof<_>)" uu___3 in
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
                   then qualified_label n f
                   else fsharp_var f in
                 let uu___2 =
                   let uu___3 = term ind' e1 in Prims.strcat " = " uu___3 in
                 Prims.strcat uu___1 uu___2) fs in
      let one =
        Prims.strcat "{ "
          (Prims.strcat (FStarC_String.concat "; " parts) " }") in
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
             (FStarC_String.concat (Prims.strcat ";\n" ind') parts) " }")
  | FStarC_Custard_Syntax.EProj (e1, n, f) when
      let uu___ = tuple_arity n in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let k =
        let uu___ = tuple_arity n in
        match uu___ with | FStar_Pervasives_Native.Some v -> v in
      let pre = "(match " in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre in term uu___2 e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = by_position k "_" [(f, "custard_tup")] in
              FStarC_String.concat ", " uu___5 in
            Prims.strcat uu___4 ") -> custard_tup)" in
          Prims.strcat " with (" uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat pre uu___
  | FStarC_Custard_Syntax.EProj (e1, n, f) ->
      let uu___ =
        let uu___1 =
          let uu___2 = term (Prims.strcat ind " ") e1 in
          ascribe_record n f uu___2 in
        let uu___2 = let uu___3 = fsharp_var f in Prims.strcat ")." uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat "(" uu___
  | FStarC_Custard_Syntax.EDiscrim (uu___, n) when
      let uu___1 = tuple_arity n in
      match uu___1 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___2 -> false -> "true"
  | FStarC_Custard_Syntax.EDiscrim (e1, n) ->
      let arg = let uu___ = is_nullary_ctor n in if uu___ then "" else " _" in
      let pre = "(match " in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre in term uu___2 e1 in
        let uu___2 =
          let uu___3 =
            let uu___4 = ctor_ref n in
            Prims.strcat uu___4 (Prims.strcat arg " -> true | _ -> false)") in
          Prims.strcat " with " uu___3 in
        Prims.strcat uu___1 uu___2 in
      Prims.strcat pre uu___
  | FStarC_Custard_Syntax.ECast (e1, t) ->
      (match ((e1.FStarC_Custard_Syntax.ty), t) with
       | (FStarC_Custard_Syntax.TInt sw1, FStarC_Custard_Syntax.TInt sw2)
           when sw1 = sw2 -> term ind e1
       | (FStarC_Custard_Syntax.TFloat uu___, FStarC_Custard_Syntax.TFloat
          fw2) ->
           (reject_fwidth fw2;
            (let pre =
               Prims.strcat "("
                 (Prims.strcat
                    (if
                       match fw2 with
                       | FStarC_Custard_Syntax.Float32 -> true
                       | uu___2 -> false
                     then "float32"
                     else "float") " ") in
             let uu___2 =
               let uu___3 = let uu___4 = after ind pre in term uu___4 e1 in
               Prims.strcat uu___3 ")" in
             Prims.strcat pre uu___2))
       | (FStarC_Custard_Syntax.TInt uu___, FStarC_Custard_Syntax.TFloat fw2)
           ->
           (reject_fwidth fw2;
            (let pre =
               Prims.strcat "("
                 (Prims.strcat
                    (if
                       match fw2 with
                       | FStarC_Custard_Syntax.Float32 -> true
                       | uu___2 -> false
                     then "float32"
                     else "float") " ") in
             let uu___2 =
               let uu___3 = let uu___4 = after ind pre in term uu___4 e1 in
               Prims.strcat uu___3 ")" in
             Prims.strcat pre uu___2))
       | (uu___, FStarC_Custard_Syntax.TInt sw2) ->
           let pre =
             let uu___1 =
               let uu___2 = int_conv sw2 in Prims.strcat uu___2 " " in
             Prims.strcat "(" uu___1 in
           let uu___1 =
             let uu___2 = let uu___3 = after ind pre in term uu___3 e1 in
             Prims.strcat uu___2 ")" in
           Prims.strcat pre uu___1
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
        let pre = "(ref " in
        let uu___2 =
          let uu___3 = let uu___4 = after ind pre in term uu___4 init in
          Prims.strcat uu___3 ")" in
        Prims.strcat pre uu___2
      else
        (let pre = "(Array.create " in
         let pre1 =
           let uu___2 =
             let uu___3 = let uu___4 = after ind pre in index uu___4 len in
             Prims.strcat uu___3 " " in
           Prims.strcat pre uu___2 in
         let uu___2 =
           let uu___3 = let uu___4 = after ind pre1 in term uu___4 init in
           Prims.strcat uu___3 ")" in
         Prims.strcat pre1 uu___2)
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
        let uu___1 =
          let uu___2 = term (Prims.strcat ind "  ") b in
          Prims.strcat uu___2 ").Value)" in
        Prims.strcat "((" uu___1
      else
        (let pre = "((" in
         let pre1 =
           let uu___1 =
             let uu___2 = let uu___3 = after ind pre in term uu___3 b in
             Prims.strcat uu___2 ").[" in
           Prims.strcat pre uu___1 in
         let uu___1 =
           let uu___2 = let uu___3 = after ind pre1 in index uu___3 i in
           Prims.strcat uu___2 "])" in
         Prims.strcat pre1 uu___1)
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
        let pre = "((" in
        let pre1 =
          let uu___1 =
            let uu___2 = let uu___3 = after ind pre in term uu___3 b in
            Prims.strcat uu___2 ").Value <- " in
          Prims.strcat pre uu___1 in
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre1 in term uu___3 v in
          Prims.strcat uu___2 ")" in
        Prims.strcat pre1 uu___1
      else
        (let pre = "((" in
         let pre1 =
           let uu___1 =
             let uu___2 = let uu___3 = after ind pre in term uu___3 b in
             Prims.strcat uu___2 ").[" in
           Prims.strcat pre uu___1 in
         let pre2 =
           let uu___1 =
             let uu___2 = let uu___3 = after ind pre1 in index uu___3 i in
             Prims.strcat uu___2 "] <- " in
           Prims.strcat pre1 uu___1 in
         let uu___1 =
           let uu___2 = let uu___3 = after ind pre2 in term uu___3 v in
           Prims.strcat uu___2 ")" in
         Prims.strcat pre2 uu___1)
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
      then
        let uu___1 =
          let uu___2 = ty e.FStarC_Custard_Syntax.ty in
          Prims.strcat uu___2 ">)" in
        Prims.strcat "(Unchecked.defaultof<" uu___1
      else "([||])"
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
        let pre = "(isNull (box " in
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre in term uu___3 b in
          Prims.strcat uu___2 "))" in
        Prims.strcat pre uu___1
      else
        (let pre = "((Array.length " in
         let uu___1 =
           let uu___2 = let uu___3 = after ind pre in term uu___3 b in
           Prims.strcat uu___2 ") = 0)" in
         Prims.strcat pre uu___1)
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufBlit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       src::si::dst::di::len::[])
      ->
      let pre = "(Array.blit " in
      let pre1 =
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre in term uu___3 src in
          Prims.strcat uu___2 " " in
        Prims.strcat pre uu___1 in
      let pre2 =
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre1 in index uu___3 si in
          Prims.strcat uu___2 " " in
        Prims.strcat pre1 uu___1 in
      let pre3 =
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre2 in term uu___3 dst in
          Prims.strcat uu___2 " " in
        Prims.strcat pre2 uu___1 in
      let pre4 =
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre3 in index uu___3 di in
          Prims.strcat uu___2 " " in
        Prims.strcat pre3 uu___1 in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre4 in index uu___3 len in
        Prims.strcat uu___2 ")" in
      Prims.strcat pre4 uu___1
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufSub;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       uu___1)
      ->
      "(failwith \"Custard: pointer arithmetic has no F# representation\")"
  | FStarC_Custard_Syntax.EOp
      ({ FStarC_Custard_Syntax.po_op = FStarC_Custard_Syntax.BufLit;
         FStarC_Custard_Syntax.po_ty = uu___;_},
       elems)
      ->
      let uu___1 = join_at ind "[| " "; " term elems in
      Prims.strcat uu___1 " |]"
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
           (before, after');
         FStarC_Custard_Syntax.po_ty = uu___;_},
       b::[])
      ->
      let pre = Prims.strcat "((* " (Prims.strcat before " *) ") in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre in term uu___3 b in
        Prims.strcat uu___2
          (Prims.strcat " (* " (Prims.strcat after' " *))")) in
      Prims.strcat pre uu___1
  | FStarC_Custard_Syntax.EOp (op, a::b::[]) when
      is_shift op.FStarC_Custard_Syntax.po_op ->
      let s =
        if
          match op.FStarC_Custard_Syntax.po_op with
          | FStarC_Custard_Syntax.BShiftL -> true
          | uu___ -> false
        then " <<< "
        else " >>> " in
      let pre = "(" in
      let pre1 =
        let uu___ =
          let uu___1 = let uu___2 = after ind pre in term uu___2 a in
          Prims.strcat uu___1 s in
        Prims.strcat pre uu___ in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre1 in index uu___2 b in
        Prims.strcat uu___1 ")" in
      Prims.strcat pre1 uu___
  | FStarC_Custard_Syntax.EOp (op, a::b::[]) when
      let uu___ =
        binop (FStarC_Custard_Syntax.at_int_width op)
          op.FStarC_Custard_Syntax.po_op in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      ((match op.FStarC_Custard_Syntax.po_ty with
        | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat fw) ->
            reject_fwidth fw
        | uu___1 -> ());
       (let pre = "(" in
        let pre1 =
          let uu___1 =
            let uu___2 = let uu___3 = after ind pre in term uu___3 a in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    binop (FStarC_Custard_Syntax.at_int_width op)
                      op.FStarC_Custard_Syntax.po_op in
                  match uu___6 with | FStar_Pervasives_Native.Some v -> v in
                Prims.strcat uu___5 " " in
              Prims.strcat " " uu___4 in
            Prims.strcat uu___2 uu___3 in
          Prims.strcat pre uu___1 in
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre1 in term uu___3 b in
          Prims.strcat uu___2 ")" in
        Prims.strcat pre1 uu___1))
  | FStarC_Custard_Syntax.EOp (op, a::[]) when
      match op.FStarC_Custard_Syntax.po_ty with
      | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw) ->
          let uu___ = w128_unop sw op.FStarC_Custard_Syntax.po_op in
          (match uu___ with
           | FStar_Pervasives_Native.Some v -> true
           | uu___1 -> false)
      | uu___ -> false ->
      let sw =
        match op.FStarC_Custard_Syntax.po_ty with
        | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PInt sw1) ->
            sw1 in
      let pre =
        let uu___ =
          let uu___1 =
            let uu___2 = w128_unop sw op.FStarC_Custard_Syntax.po_op in
            match uu___2 with | FStar_Pervasives_Native.Some v -> v in
          Prims.strcat uu___1 " " in
        Prims.strcat "(" uu___ in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre in term uu___2 a in
        Prims.strcat uu___1 ")" in
      Prims.strcat pre uu___
  | FStarC_Custard_Syntax.EOp (op, a::[]) when
      let uu___ =
        unop (FStarC_Custard_Syntax.at_int_width op)
          op.FStarC_Custard_Syntax.po_op in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      ((match op.FStarC_Custard_Syntax.po_ty with
        | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.PFloat fw) ->
            reject_fwidth fw
        | uu___1 -> ());
       (let pre =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                unop (FStarC_Custard_Syntax.at_int_width op)
                  op.FStarC_Custard_Syntax.po_op in
              match uu___3 with | FStar_Pervasives_Native.Some v -> v in
            Prims.strcat uu___2 " " in
          Prims.strcat "(" uu___1 in
        let uu___1 =
          let uu___2 = let uu___3 = after ind pre in term uu___3 a in
          Prims.strcat uu___2 ")" in
        Prims.strcat pre uu___1))
  | FStarC_Custard_Syntax.EOp (op, args) -> no_operator op
  | FStarC_Custard_Syntax.EAny ->
      let uu___ =
        let uu___1 = ty e.FStarC_Custard_Syntax.ty in
        Prims.strcat uu___1 ">)" in
      Prims.strcat "(Unchecked.defaultof<" uu___
  | FStarC_Custard_Syntax.EAbort s ->
      let uu___ = let uu___1 = escape s in Prims.strcat uu___1 "\")" in
      Prims.strcat "(failwith \"" uu___
  | FStarC_Custard_Syntax.EWhile (c, body) ->
      let pre = "(while " in
      let hd =
        let uu___ =
          let uu___1 = let uu___2 = after ind pre in term uu___2 c in
          Prims.strcat uu___1 " do\n" in
        Prims.strcat pre uu___ in
      let ind' = Prims.strcat ind "   " in
      let uu___ =
        let uu___1 = let uu___2 = term ind' body in Prims.strcat uu___2 ")" in
        Prims.strcat ind' uu___1 in
      Prims.strcat hd uu___
  | FStarC_Custard_Syntax.ERaise e1 ->
      let pre = "(raise " in
      let uu___ =
        let uu___1 = let uu___2 = after ind pre in term uu___2 e1 in
        Prims.strcat uu___1 ")" in
      Prims.strcat pre uu___
  | FStarC_Custard_Syntax.ETry (e1, brs) ->
      let pre = "(try " in
      let hd =
        let uu___ =
          let uu___1 = let uu___2 = after ind pre in term uu___2 e1 in
          Prims.strcat uu___1 " with\n" in
        Prims.strcat pre uu___ in
      let ind' = Prims.strcat ind " " in
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_List.map (case ind') brs in
          FStarC_String.concat "\n" uu___2 in
        Prims.strcat uu___1 ")" in
      Prims.strcat hd uu___
and no_operator (_op : FStarC_Custard_Syntax.prim_op) : Prims.string=
  FStarC_Effect.failwith
    "Custard: an operator reached the F# backend at an arity it has no spelling for"
and coerce (ind : Prims.string) (e1 : FStarC_Custard_Syntax.expr)
  (t : FStarC_Custard_Syntax.cty) : Prims.string=
  match ((e1.FStarC_Custard_Syntax.ty), t) with
  | (FStarC_Custard_Syntax.TAny, FStarC_Custard_Syntax.TAny) -> term ind e1
  | (uu___, FStarC_Custard_Syntax.TAny) ->
      let pre = "(box " in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre in term uu___3 e1 in
        Prims.strcat uu___2 ")" in
      Prims.strcat pre uu___1
  | (a, b) when erased_pun a b -> reject_coercion a b
  | (FStarC_Custard_Syntax.TAny, uu___) ->
      let pre =
        let uu___1 = let uu___2 = ty t in Prims.strcat uu___2 "> " in
        Prims.strcat "(unbox<" uu___1 in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre in term uu___3 e1 in
        Prims.strcat uu___2 ")" in
      Prims.strcat pre uu___1
  | uu___ ->
      let pre =
        let uu___1 = let uu___2 = ty t in Prims.strcat uu___2 "> (box " in
        Prims.strcat "(unbox<" uu___1 in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre in term uu___3 e1 in
        Prims.strcat uu___2 "))" in
      Prims.strcat pre uu___1
and index (ind : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.EConst (FStarC_Custard_Syntax.CInt
      (v, b, FStar_Pervasives_Native.Some sw)) when Prims.not (is_w128 sw) ->
      FStarC_Custard_Syntax.int_lit_to_string v b
  | FStarC_Custard_Syntax.ECoerce (e1, uu___) -> index ind e1
  | FStarC_Custard_Syntax.ECast (e1, t) when
      match ((e1.FStarC_Custard_Syntax.ty), t) with
      | (FStarC_Custard_Syntax.TInt a, FStarC_Custard_Syntax.TInt b) ->
          value_preserving a b
      | uu___ -> false -> index ind e1
  | uu___ ->
      let pre = "(int " in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre in term uu___3 e in
        Prims.strcat uu___2 ")" in
      Prims.strcat pre uu___1
and stmts (ind : Prims.string) (e : FStarC_Custard_Syntax.expr) :
  Prims.string=
  match e.FStarC_Custard_Syntax.e with
  | FStarC_Custard_Syntax.ELet (x, uu___, e1, e2) ->
      let pre =
        let uu___1 = let uu___2 = fsharp_local x in Prims.strcat uu___2 " = " in
        Prims.strcat "let " uu___1 in
      let uu___1 =
        let uu___2 = let uu___3 = after ind pre in term uu___3 e1 in
        let uu___3 =
          let uu___4 = let uu___5 = stmts ind e2 in Prims.strcat ind uu___5 in
          Prims.strcat " in\n" uu___4 in
        Prims.strcat uu___2 uu___3 in
      Prims.strcat pre uu___1
  | FStarC_Custard_Syntax.ESeq (e1, e2) ->
      let s = term ind e1 in
      let s1 =
        if
          match e1.FStarC_Custard_Syntax.ty with
          | FStarC_Custard_Syntax.TUnit -> true
          | uu___ -> false
        then s
        else
          (let pre = "(ignore " in
           let uu___ =
             let uu___1 = let uu___2 = after ind pre in term uu___2 e1 in
             Prims.strcat uu___1 ")" in
           Prims.strcat pre uu___) in
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
                      let uu___4 = fsharp_local x in
                      let uu___5 =
                        let uu___6 = constant c in Prims.strcat " = " uu___6 in
                      Prims.strcat uu___4 uu___5) eqs in
           let pre =
             let uu___3 = let uu___4 = pattern p1 in Prims.strcat "| " uu___4 in
             Prims.strcat ind uu___3 in
           let pre1 =
             match (conds, g) with
             | ([], FStar_Pervasives_Native.None) -> Prims.strcat pre " -> "
             | uu___3 ->
                 let pre2 =
                   Prims.strcat pre
                     (Prims.strcat " when "
                        (FStarC_String.concat " && " conds)) in
                 (match g with
                  | FStar_Pervasives_Native.None -> Prims.strcat pre2 " -> "
                  | FStar_Pervasives_Native.Some g1 ->
                      let pre3 =
                        Prims.strcat pre2 (if conds = [] then "" else " && ") in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = col_after Prims.int_zero pre3 in
                            spaces uu___7 in
                          term uu___6 g1 in
                        Prims.strcat uu___5 " -> " in
                      Prims.strcat pre3 uu___4) in
           let col = col_after Prims.int_zero pre1 in
           if col > (line_width / (Prims.of_int 2))
           then
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 = term (Prims.strcat ind "    ") b in
                   Prims.strcat "    " uu___6 in
                 Prims.strcat ind uu___5 in
               Prims.strcat "\n" uu___4 in
             Prims.strcat pre1 uu___3
           else
             (let uu___3 = let uu___4 = spaces col in term uu___4 b in
              Prims.strcat pre1 uu___3))
let params (ps : Prims.string Prims.list) : Prims.string=
  match ps with
  | [] -> ""
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_List.map
              (fun p -> let uu___4 = fsharp_var p in Prims.strcat "'" uu___4)
              ps in
          FStarC_String.concat ", " uu___3 in
        Prims.strcat uu___2 ">" in
      Prims.strcat "<" uu___1
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
             let uu___2 = fsharp_type_name t.FStarC_Custard_Syntax.dt_name in
             let uu___3 = params t.FStarC_Custard_Syntax.dt_params in
             Prims.strcat uu___2 uu___3 in
           Prims.strcat (if first then "type " else "and ") uu___1 in
         match t.FStarC_Custard_Syntax.dt_body with
         | FStarC_Custard_Syntax.TAbstract ->
             FStar_Pervasives_Native.Some (Prims.strcat hd " = obj")
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
                                  let uu___8 = fsharp_var f in
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
          let uu___2 = fsharp_ctor_ident e.FStarC_Custard_Syntax.de_name in
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
                 let uu___2 = fsharp_local b.FStarC_Custard_Syntax.b_name in
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
      let hd =
        let uu___ =
          let uu___1 = fsharp_value_name l.FStarC_Custard_Syntax.dl_name in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = ty l.FStarC_Custard_Syntax.dl_ret in
                Prims.strcat uu___5 " =\n  " in
              Prims.strcat " : " uu___4 in
            Prims.strcat bs uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat kw uu___ in
      let uu___ =
        let uu___1 = term "  " l.FStarC_Custard_Syntax.dl_body in
        Prims.strcat hd uu___1 in
      FStar_Pervasives_Native.Some uu___
let supported_realizations : (Prims.string * Prims.string) Prims.list=
  [("Prims.op_Plus", "Prims.op_Plus");
  ("Prims.op_Minus", "Prims.op_Minus");
  ("Prims.op_Star", "Prims.op_Star");
  ("Prims.op_Slash", "Prims.op_Slash");
  ("Prims.op_Percent", "Prims.op_Percent");
  ("Prims.op_Minus_Minus", "Prims.op_Minus_Minus");
  ("Prims.op_Less", "Prims.op_Less");
  ("Prims.op_Less_Equals", "Prims.op_Less_Equals");
  ("Prims.op_Greater", "Prims.op_Greater");
  ("Prims.op_Greater_Equals", "Prims.op_Greater_Equals");
  ("Prims.abs", "Prims.abs");
  ("Prims.pow2", "Prims.pow2");
  ("Prims.strcat", "Prims.strcat");
  ("Prims.op_Hat", "Prims.strcat");
  ("Prims.string_of_bool", "Prims.string_of_bool");
  ("Prims.string_of_int", "Prims.string_of_int");
  ("FStar.List.Tot.Base.isEmpty", "FStar_List_Tot_Base.isEmpty");
  ("FStar.List.Tot.Base.hd", "FStar_List_Tot_Base.hd");
  ("FStar.List.Tot.Base.tail", "FStar_List_Tot_Base.tail");
  ("FStar.List.Tot.Base.tl", "FStar_List_Tot_Base.tl");
  ("FStar.List.Tot.Base.last", "FStar_List_Tot_Base.last");
  ("FStar.List.Tot.Base.init", "FStar_List_Tot_Base.init");
  ("FStar.List.Tot.Base.length", "FStar_List_Tot_Base.length");
  ("FStar.List.Tot.Base.nth", "FStar_List_Tot_Base.nth");
  ("FStar.List.Tot.Base.index", "FStar_List_Tot_Base.index");
  ("FStar.List.Tot.Base.count", "FStar_List_Tot_Base.count");
  ("FStar.List.Tot.Base.rev_acc", "FStar_List_Tot_Base.rev_acc");
  ("FStar.List.Tot.Base.rev", "FStar_List_Tot_Base.rev");
  ("FStar.List.Tot.Base.append", "FStar_List_Tot_Base.append");
  ("FStar.List.Tot.Base.snoc", "FStar_List_Tot_Base.snoc");
  ("FStar.List.Tot.Base.flatten", "FStar_List_Tot_Base.flatten");
  ("FStar.List.Tot.Base.map", "FStar_List_Tot_Base.map");
  ("FStar.List.Tot.Base.mapi", "FStar_List_Tot_Base.mapi");
  ("FStar.List.Tot.Base.concatMap", "FStar_List_Tot_Base.concatMap");
  ("FStar.List.Tot.Base.fold_left", "FStar_List_Tot_Base.fold_left");
  ("FStar.List.Tot.Base.fold_right", "FStar_List_Tot_Base.fold_right");
  ("FStar.List.Tot.Base.fold_left2", "FStar_List_Tot_Base.fold_left2");
  ("FStar.List.Tot.Base.mem", "FStar_List_Tot_Base.mem");
  ("FStar.List.Tot.Base.contains", "FStar_List_Tot_Base.contains");
  ("FStar.List.Tot.Base.existsb", "FStar_List_Tot_Base.existsb");
  ("FStar.List.Tot.Base.find", "FStar_List_Tot_Base.find");
  ("FStar.List.Tot.Base.filter", "FStar_List_Tot_Base.filter");
  ("FStar.List.Tot.Base.for_all", "FStar_List_Tot_Base.for_all");
  ("FStar.List.Tot.Base.collect", "FStar_List_Tot_Base.collect");
  ("FStar.List.Tot.Base.tryFind", "FStar_List_Tot_Base.tryFind");
  ("FStar.List.Tot.Base.tryPick", "FStar_List_Tot_Base.tryPick");
  ("FStar.List.Tot.Base.choose", "FStar_List_Tot_Base.choose");
  ("FStar.List.Tot.Base.partition", "FStar_List_Tot_Base.partition");
  ("FStar.List.Tot.Base.noRepeats", "FStar_List_Tot_Base.noRepeats");
  ("FStar.List.Tot.Base.assoc", "FStar_List_Tot_Base.assoc");
  ("FStar.List.Tot.Base.split", "FStar_List_Tot_Base.split");
  ("FStar.List.Tot.Base.unzip", "FStar_List_Tot_Base.unzip");
  ("FStar.List.Tot.Base.unzip3", "FStar_List_Tot_Base.unzip3");
  ("FStar.List.Tot.Base.splitAt", "FStar_List_Tot_Base.splitAt");
  ("FStar.List.Tot.Base.unsnoc", "FStar_List_Tot_Base.unsnoc");
  ("FStar.List.Tot.Base.split3", "FStar_List_Tot_Base.split3");
  ("FStar.List.Tot.Base.bool_of_compare",
    "FStar_List_Tot_Base.bool_of_compare");
  ("FStar.List.Tot.Base.compare_of_bool",
    "FStar_List_Tot_Base.compare_of_bool");
  ("FStar.List.Tot.Base.sortWith", "FStar_List_Tot_Base.sortWith");
  ("FStar.List.Tot.Base.subset", "FStar_List_Tot_Base.subset");
  ("FStar.List.Tot.Base.list_unref", "FStar_List_Tot_Base.list_unref");
  ("FStar.List.Tot.Base.list_ref", "FStar_List_Tot_Base.list_ref");
  ("FStar.List.Tot.Base.list_refb", "FStar_List_Tot_Base.list_refb");
  ("FStar.List.Tot.Base.op_At", "FStar_List_Tot_Base.append");
  ("FStar.UInt8.to_string", "Prims.string_of_int8");
  ("FStar.UInt16.to_string", "Prims.string_of_int16");
  ("FStar.UInt32.to_string", "Prims.string_of_int32");
  ("FStar.UInt64.to_string", "Prims.string_of_int64");
  ("FStar.Int8.to_string", "Prims.string_of_sint8");
  ("FStar.Int16.to_string", "Prims.string_of_sint16");
  ("FStar.Int32.to_string", "Prims.string_of_sint32");
  ("FStar.Int64.to_string", "Prims.string_of_sint64");
  ("FStar.IO.print_newline", "FStar_IO.print_newline");
  ("FStar.IO.print_string", "FStar_IO.print_string");
  ("FStar.IO.print_uint8", "FStar_IO.print_uint8");
  ("FStar.IO.print_uint16", "FStar_IO.print_uint16");
  ("FStar.IO.print_uint32", "FStar_IO.print_uint32");
  ("FStar.IO.print_uint64", "FStar_IO.print_uint64");
  ("FStar.IO.print_uint8_dec", "FStar_IO.print_uint8_dec");
  ("FStar.IO.print_uint16_dec", "FStar_IO.print_uint16_dec");
  ("FStar.IO.print_uint32_dec", "FStar_IO.print_uint32_dec");
  ("FStar.IO.print_uint64_dec", "FStar_IO.print_uint64_dec");
  ("FStar.IO.print_uint8_hex_pad", "FStar_IO.print_uint8_hex_pad");
  ("FStar.IO.print_uint16_hex_pad", "FStar_IO.print_uint16_hex_pad");
  ("FStar.IO.print_uint32_hex_pad", "FStar_IO.print_uint32_hex_pad");
  ("FStar.IO.print_uint64_hex_pad", "FStar_IO.print_uint64_hex_pad");
  ("FStar.IO.print_uint8_dec_pad", "FStar_IO.print_uint8_dec_pad");
  ("FStar.IO.print_uint16_dec_pad", "FStar_IO.print_uint16_dec_pad");
  ("FStar.IO.print_uint32_dec_pad", "FStar_IO.print_uint32_dec_pad");
  ("FStar.IO.print_uint64_dec_pad", "FStar_IO.print_uint64_dec_pad");
  ("FStar.IO.debug_print_string", "FStar_IO.debug_print_string")]
let supported_realization (n : FStarC_Custard_Syntax.name) :
  Prims.string FStar_Pervasives_Native.option=
  if
    match n.FStarC_Custard_Syntax.spec with
    | FStar_Pervasives_Native.Some v -> true
    | uu___ -> false
  then FStar_Pervasives_Native.None
  else
    FStarC_List.tryPick
      (fun uu___ ->
         match uu___ with
         | (k, v) ->
             let uu___1 =
               let uu___2 = FStarC_Custard_Syntax.string_of_name n in
               k = uu___2 in
             if uu___1
             then FStar_Pervasives_Native.Some v
             else FStar_Pervasives_Native.None) supported_realizations
let reject_unrealized (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DExternal e when
           if
             match e.FStarC_Custard_Syntax.dx_target with
             | FStar_Pervasives_Native.None -> true
             | uu___ -> false
           then
             let uu___ =
               supported_realization e.FStarC_Custard_Syntax.dx_name in
             match uu___ with
             | FStar_Pervasives_Native.None -> true
             | uu___1 -> false
           else false ->
           let m =
             FStarC_String.concat "."
               (e.FStarC_Custard_Syntax.dx_name).FStarC_Custard_Syntax.ns in
           let uu___ =
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Custard_Syntax.string_of_name
                       e.FStarC_Custard_Syntax.dx_name in
                   Prims.strcat uu___4
                     " has no F* definition and no F# realization." in
                 Prims.strcat "Custard: " uu___3 in
               text uu___2 in
             [uu___1;
             text
               (Prims.strcat "It is declared by "
                  (Prims.strcat m
                     ", which F* realizes with hand-written OCaml in ulib/ml.  The F# backend compiles to .NET's own types rather than to that library, so it accepts the programs the C backend accepts and not the ones the OCaml backend accepts (section 122)."));
             text
               "Give it a target with [@@custard_extern \"...\"] and supply that name yourself, or extract this program with --custard_backend OCaml."] in
           FStarC_Errors.raise_error0
             FStarC_Errors_Codes.Error_CustardNoFSharpRealization ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___)
       | uu___ -> ()) p
let reject_realized_types (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t when
           let uu___ =
             let uu___1 =
               FStarC_Custard_Syntax.has_flag
                 t.FStarC_Custard_Syntax.dt_flags
                 FStarC_Custard_Syntax.Realized in
             if uu___1
             then
               let uu___2 = is_builtin_type t.FStarC_Custard_Syntax.dt_name in
               Prims.not uu___2
             else false in
           if uu___
           then
             let uu___1 = is_tuple_type t.FStarC_Custard_Syntax.dt_name in
             Prims.not uu___1
           else false ->
           let uu___ =
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Custard_Syntax.string_of_name
                       t.FStarC_Custard_Syntax.dt_name in
                   Prims.strcat uu___4
                     " is realized by hand-written OCaml and has no F# realization." in
                 Prims.strcat "Custard: the type " uu___3 in
               text uu___2 in
             [uu___1;
             text
               "Its declaration says what shape the type has, but not what it is: the definition is in ulib/ml, and there is no F# counterpart of that library (section 122.9).";
             text
               "Extract this program with --custard_backend OCaml, or keep it to the fragment the C backend compiles."] in
           FStarC_Errors.raise_error0
             FStarC_Errors_Codes.Error_CustardNoFSharpRealization ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___)
       | uu___ -> ()) p
let reject_target_only_types (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType t ->
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
                                t.FStarC_Custard_Syntax.dt_name in
                            Prims.strcat uu___5
                              " has a template target, and templates reached the F# backend." in
                          Prims.strcat "Custard: the external type " uu___4 in
                        text uu___3 in
                      [uu___2;
                      text
                        (Prims.strcat "Its target spelling ["
                           (Prims.strcat target
                              "] has a placeholder for an argument, so two instantiations of it are two different target types; F# has no such construction.  Section 69 is a C-backend feature (--custard_backend C)."))] in
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
                                t.FStarC_Custard_Syntax.dt_name in
                            Prims.strcat uu___4
                              " is [@@custard_c_reference], and reference bindings reached the F# backend." in
                          Prims.strcat "Custard: the type " uu___3 in
                        text uu___2 in
                      [uu___1;
                      text
                        "The attribute says that values of the type are handles, so a binding of one has to alias rather than copy, which is C++ [T &x = ...] and F# has no way to spell.  Section 70.2 is a C-backend feature (--custard_backend C)."] in
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Error_CustardBadReference ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___)
                | uu___ -> ()) t.FStarC_Custard_Syntax.dt_flags
       | uu___ -> ()) p
let rec mentions_tyvar (t : FStarC_Custard_Syntax.cty) : Prims.bool=
  match t with
  | FStarC_Custard_Syntax.TVar uu___ -> true
  | FStarC_Custard_Syntax.TArrow (a, uu___, b) ->
      let uu___1 = mentions_tyvar a in
      if uu___1 then true else mentions_tyvar b
  | FStarC_Custard_Syntax.TTuple ts -> FStarC_List.existsb mentions_tyvar ts
  | FStarC_Custard_Syntax.TBuf t1 -> mentions_tyvar t1
  | FStarC_Custard_Syntax.TRef t1 -> mentions_tyvar t1
  | FStarC_Custard_Syntax.TInline t1 -> mentions_tyvar t1
  | FStarC_Custard_Syntax.TApp (uu___, args) ->
      FStarC_List.existsb mentions_tyvar args
  | uu___ -> false
let reject_generic_values (p : FStarC_Custard_Syntax.program) : unit=
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DLet l when
           if
             match l.FStarC_Custard_Syntax.dl_binders with
             | [] -> true
             | uu___ -> false
           then mentions_tyvar l.FStarC_Custard_Syntax.dl_ret
           else false ->
           let uu___ =
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStarC_Custard_Syntax.string_of_name
                       l.FStarC_Custard_Syntax.dl_name in
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = ty l.FStarC_Custard_Syntax.dl_ret in
                       Prims.strcat uu___7 " is still polymorphic." in
                     Prims.strcat
                       " is a top-level value with no parameters whose type "
                       uu___6 in
                   Prims.strcat uu___4 uu___5 in
                 Prims.strcat "Custard: " uu___3 in
               text uu___2 in
             [uu___1;
             text
               "F#'s value restriction does not generalize such a definition, so it cannot be written at all (section 122.11).  Nothing in this program specialized it, which means nothing uses it at a type either.";
             text
               "Give it a parameter, specialize it at the type it is wanted at, or extract with --custard_backend OCaml."] in
           FStarC_Errors.raise_error0
             FStarC_Errors_Codes.Error_CustardUnrepresentableValue ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___)
       | uu___ -> ()) p
let build_tables (p : FStarC_Custard_Syntax.program) : unit=
  let tbl = FStarC_SMap.create (Prims.of_int 50) in
  let tups = FStarC_SMap.create (Prims.of_int 20) in
  let nul = FStarC_SMap.create (Prims.of_int 50) in
  let recs = FStarC_SMap.create (Prims.of_int 100) in
  let labels = FStarC_SMap.create (Prims.of_int 100) in
  FStarC_List.iter
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DExternal e ->
           (match e.FStarC_Custard_Syntax.dx_target with
            | FStar_Pervasives_Native.Some t ->
                let uu___1 =
                  FStarC_Custard_Syntax.string_of_name
                    e.FStarC_Custard_Syntax.dx_name in
                FStarC_SMap.add tbl uu___1 t
            | FStar_Pervasives_Native.None ->
                let uu___1 =
                  supported_realization e.FStarC_Custard_Syntax.dx_name in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some t ->
                     let uu___2 =
                       FStarC_Custard_Syntax.string_of_name
                         e.FStarC_Custard_Syntax.dx_name in
                     FStarC_SMap.add tbl uu___2 t
                 | FStar_Pervasives_Native.None -> ()))
       | FStarC_Custard_Syntax.DExn e ->
           if
             (match e.FStarC_Custard_Syntax.de_args with
              | [] -> true
              | uu___1 -> false)
           then
             let uu___1 =
               FStarC_Custard_Syntax.string_of_name
                 e.FStarC_Custard_Syntax.de_name in
             FStarC_SMap.add nul uu___1 ()
           else ()
       | FStarC_Custard_Syntax.DType t ->
           (match t.FStarC_Custard_Syntax.dt_body with
            | FStarC_Custard_Syntax.TVariant cs ->
                (FStarC_List.iter
                   (fun uu___2 ->
                      match uu___2 with
                      | (cn, fs) ->
                          if (match fs with | [] -> true | uu___3 -> false)
                          then
                            let uu___3 =
                              FStarC_Custard_Syntax.string_of_name cn in
                            FStarC_SMap.add nul uu___3 ()
                          else ()) cs;
                 (let uu___2 = is_tuple_type t.FStarC_Custard_Syntax.dt_name in
                  if uu___2
                  then
                    match cs with
                    | (cn, fs)::[] ->
                        ((let uu___4 =
                            FStarC_Custard_Syntax.string_of_name
                              t.FStarC_Custard_Syntax.dt_name in
                          FStarC_SMap.add tups uu___4 (FStarC_List.length fs));
                         (let uu___4 =
                            FStarC_Custard_Syntax.string_of_name cn in
                          FStarC_SMap.add tups uu___4 (FStarC_List.length fs)))
                    | uu___3 -> ()
                  else ()))
            | FStarC_Custard_Syntax.TRecord fs ->
                ((let uu___2 = is_tuple_type t.FStarC_Custard_Syntax.dt_name in
                  if uu___2
                  then
                    let uu___3 =
                      FStarC_Custard_Syntax.string_of_name
                        t.FStarC_Custard_Syntax.dt_name in
                    FStarC_SMap.add tups uu___3 (FStarC_List.length fs)
                  else ());
                 (let uu___3 =
                    FStarC_Custard_Syntax.string_of_name
                      t.FStarC_Custard_Syntax.dt_name in
                  FStarC_SMap.add recs uu___3
                    (FStarC_List.length t.FStarC_Custard_Syntax.dt_params));
                 FStarC_List.iter
                   (fun uu___3 ->
                      match uu___3 with
                      | (f, uu___4) ->
                          let k = label_key t.FStarC_Custard_Syntax.dt_name f in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = FStarC_SMap.try_find labels k in
                              match uu___7 with
                              | FStar_Pervasives_Native.Some i -> i
                              | FStar_Pervasives_Native.None ->
                                  Prims.int_zero in
                            Prims.int_one + uu___6 in
                          FStarC_SMap.add labels k uu___5) fs)
            | uu___1 -> ())
       | uu___1 -> ()) p;
  FStarC_Effect.op_Colon_Equals externals tbl;
  FStarC_Effect.op_Colon_Equals tuples tups;
  FStarC_Effect.op_Colon_Equals nullary nul;
  FStarC_Effect.op_Colon_Equals record_params recs;
  FStarC_Effect.op_Colon_Equals record_labels labels
let header (m : Prims.string) : Prims.string=
  Prims.strcat "// Generated by F* Custard extraction. Do not edit.\nmodule "
    (Prims.strcat m
       "\n#nowarn \"25\" \"26\" \"40\" \"49\" \"64\" \"1182\" \"3220\"\nopen FStarCustard\n")
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
       let g = group_of d in
       let first =
         if
           match g with
           | FStar_Pervasives_Native.None -> true
           | uu___ -> false
         then true
         else (let uu___ = FStarC_Effect.op_Bang prev in g <> uu___) in
       let uu___ = print_decl first d in
       match uu___ with
       | FStar_Pervasives_Native.Some s ->
           (FStarC_Effect.op_Colon_Equals prev g; [s])
       | FStar_Pervasives_Native.None -> []) p
let entrypoints (p : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.dlet Prims.list=
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
           else false -> [l]
       | uu___ -> []) p
let entry_calls (p : FStarC_Custard_Syntax.program) :
  Prims.string Prims.list=
  let uu___ = entrypoints p in
  match uu___ with
  | [] -> []
  | ls ->
      let body =
        FStarC_List.map
          (fun l ->
             let args =
               let uu___1 =
                 FStarC_List.map (fun uu___2 -> "()")
                   l.FStarC_Custard_Syntax.dl_binders in
               FStarC_String.concat " " uu___1 in
             let call =
               let uu___1 =
                 let uu___2 =
                   fsharp_value_name l.FStarC_Custard_Syntax.dl_name in
                 Prims.strcat uu___2
                   (Prims.strcat " " (Prims.strcat args ")")) in
               Prims.strcat "(" uu___1 in
             match l.FStarC_Custard_Syntax.dl_ret with
             | FStarC_Custard_Syntax.TInt uu___1 ->
                 Prims.strcat "  (int " (Prims.strcat call ")")
             | FStarC_Custard_Syntax.TUnit ->
                 Prims.strcat "  " (Prims.strcat call "\n  0")
             | uu___1 ->
                 Prims.strcat "  (ignore " (Prims.strcat call ")\n  0")) ls in
      [Prims.strcat "[<EntryPoint>]\nlet main (_argv : string[]) : int =\n"
         (FStarC_String.concat "\n" body)]
let assemble (m : Prims.string) (ds : Prims.string Prims.list) :
  Prims.string=
  Prims.strcat (header m)
    (Prims.strcat "\n" (Prims.strcat (FStarC_String.concat "\n\n" ds) "\n"))
let reserve_top (p : FStarC_Custard_Syntax.program) : unit=
  let uu___ =
    FStarC_List.collect
      (fun d ->
         match d with
         | FStarC_Custard_Syntax.DLet l ->
             let uu___1 = fsharp_value_name l.FStarC_Custard_Syntax.dl_name in
             [uu___1]
         | FStarC_Custard_Syntax.DExternal e ->
             let uu___1 = fsharp_value_name e.FStarC_Custard_Syntax.dx_name in
             [uu___1]
         | uu___1 -> []) p in
  FStarC_Effect.op_Colon_Equals reserved_top uu___
let print_program (stem : Prims.string) (p : FStarC_Custard_Syntax.program) :
  Prims.string=
  reject_target_only_types p;
  reject_realized_types p;
  reject_unrealized p;
  reject_generic_values p;
  build_tables p;
  reserve_top p;
  (let uu___6 = module_name_of_unit stem in
   let uu___7 =
     let uu___8 = print_decls p in
     let uu___9 = entry_calls p in FStarC_List.op_At uu___8 uu___9 in
   assemble uu___6 uu___7)
let runtime_source : Prims.string=
  "// Generated by F* Custard extraction. Do not edit.\n//\n// The Custard F# support library.  See section 122.8 of\n// doc/ref/custard.md.  It holds exactly what .NET does not already\n// supply under the name F* declares: the Prims operators on bigint, two\n// 128-bit conversions that have no inline spelling, and FStar.IO.\nmodule FStarCustard\n\nopen System\n\n// A widening conversion into a 128-bit integer has to know the sign of\n// what it came from -- FStar.Int.Cast.Full specifies the result mod\n// 2^128, so a negative source sets the high bits -- and F# resolves an\n// op_Implicit on the argument type, which at a type variable it cannot\n// see.  These two do the resolving with an explicit conversion through\n// the widest same-signed type, which is exact in both directions.\nlet inline toU128 (x : ^a) : UInt128 =\n  UInt128.CreateTruncating x\n\nlet inline toI128 (x : ^a) : Int128 =\n  Int128.CreateTruncating x\n\n// F#'s ~~~ resolves against op_LogicalNot, which the 128-bit types do not\n// define even though they define every other bitwise operator.  The\n// complement of x is x xor all-ones, and for a signed one it is -x - 1.\nlet notU128 (x : UInt128) : UInt128 = UInt128.MaxValue ^^^ x\nlet notI128 (x : Int128) : Int128 = -x - Int128.One\n\n// Section 122.13.  Prims.int is bigint, so these are the .NET operators\n// under the names F* declares for them.\nmodule Prims =\n  let op_Plus (x : bigint) (y : bigint) : bigint = x + y\n  let op_Minus (x : bigint) (y : bigint) : bigint = x - y\n  let op_Star (x : bigint) (y : bigint) : bigint = x * y\n  let op_Slash (x : bigint) (y : bigint) : bigint = x / y\n  let op_Percent (x : bigint) (y : bigint) : bigint = x % y\n  let op_Minus_Minus (x : bigint) : bigint = -x\n  let op_Less (x : bigint) (y : bigint) : bool = x < y\n  let op_Less_Equals (x : bigint) (y : bigint) : bool = x <= y\n  let op_Greater (x : bigint) (y : bigint) : bool = x > y\n  let op_Greater_Equals (x : bigint) (y : bigint) : bool = x >= y\n  let abs (x : bigint) : bigint = if x < 0I then -x else x\n  let pow2 (n : bigint) : bigint =\n    System.Numerics.BigInteger.Pow (2I, int n)\n  let strcat (x : string) (y : string) : string = x + y\n  let string_of_bool (b : bool) : string = if b then \"true\" else \"false\"\n  let string_of_int (x : bigint) : string = x.ToString ()\n  let string_of_int8 (x : uint8) : string = x.ToString ()\n  let string_of_int16 (x : uint16) : string = x.ToString ()\n  let string_of_int32 (x : uint32) : string = x.ToString ()\n  let string_of_int64 (x : uint64) : string = x.ToString ()\n  let string_of_sint8 (x : int8) : string = x.ToString ()\n  let string_of_sint16 (x : int16) : string = x.ToString ()\n  let string_of_sint32 (x : int32) : string = x.ToString ()\n  let string_of_sint64 (x : int64) : string = x.ToString ()\n\n// Section 122.13.  Prims.list is F#'s own list, so FStar.List.Tot.Base is a\n// line-for-line translation of the OCaml realization rather than anything\n// this backend had to invent.\nmodule FStar_List_Tot_Base =\n  let isEmpty (l : 'a list) : bool = List.isEmpty l\n  let hd (l : 'a list) : 'a = List.head l\n  let tail (l : 'a list) : 'a list = List.tail l\n  let tl (l : 'a list) : 'a list = List.tail l\n  let last (l : 'a list) : 'a = List.last l\n  let init (l : 'a list) : 'a list = List.truncate (List.length l - 1) l\n  let length (l : 'a list) : bigint = bigint (List.length l)\n  let nth (l : 'a list) (i : bigint) : 'a option =\n    if i < 0I || i >= bigint (List.length l) then None\n    else Some (List.item (int i) l)\n  let index (l : 'a list) (i : bigint) : 'a = List.item (int i) l\n  let count (x : 'a) (l : 'a list) : bigint =\n    bigint (List.length (List.filter (fun y -> y = x) l))\n  let rev_acc (l : 'a list) (r : 'a list) : 'a list = List.rev l @ r\n  let rev (l : 'a list) : 'a list = List.rev l\n  let append (l : 'a list) (r : 'a list) : 'a list = l @ r\n  let snoc ((l : 'a list), (x : 'a)) : 'a list = l @ [x]\n  let flatten (l : 'a list list) : 'a list = List.concat l\n  let map (f : 'a -> 'b) (l : 'a list) : 'b list = List.map f l\n  let mapi (f : bigint -> 'a -> 'b) (l : 'a list) : 'b list =\n    List.mapi (fun i x -> f (bigint i) x) l\n  let concatMap (f : 'a -> 'b list) (l : 'a list) : 'b list = List.collect f l\n  let fold_left (f : 'a -> 'b -> 'a) (z : 'a) (l : 'b list) : 'a =\n    List.fold f z l\n  let fold_right (f : 'a -> 'b -> 'b) (l : 'a list) (z : 'b) : 'b =\n    List.foldBack f l z\n  let fold_left2 (f : 'a -> 'b -> 'c -> 'a) (z : 'a) (l : 'b list)\n                 (m : 'c list) : 'a = List.fold2 f z l m\n  let mem (x : 'a) (l : 'a list) : bool = List.contains x l\n  let contains (x : 'a) (l : 'a list) : bool = List.contains x l\n  let existsb (f : 'a -> bool) (l : 'a list) : bool = List.exists f l\n  let find (f : 'a -> bool) (l : 'a list) : 'a option = List.tryFind f l\n  let filter (f : 'a -> bool) (l : 'a list) : 'a list = List.filter f l\n  let for_all (f : 'a -> bool) (l : 'a list) : bool = List.forall f l\n  let collect (f : 'a -> 'b list) (l : 'a list) : 'b list = List.collect f l\n  let tryFind (f : 'a -> bool) (l : 'a list) : 'a option = List.tryFind f l\n  let tryPick (f : 'a -> 'b option) (l : 'a list) : 'b option = List.tryPick f l\n  let choose (f : 'a -> 'b option) (l : 'a list) : 'b list = List.choose f l\n  let partition (f : 'a -> bool) (l : 'a list) : 'a list * 'a list =\n    List.partition f l\n  let noRepeats (l : 'a list) : bool =\n    List.length (List.distinct l) = List.length l\n  let assoc (x : 'a) (l : ('a * 'b) list) : 'b option =\n    List.tryPick (fun (k, v) -> if k = x then Some v else None) l\n  let split (l : ('a * 'b) list) : 'a list * 'b list = List.unzip l\n  let unzip (l : ('a * 'b) list) : 'a list * 'b list = List.unzip l\n  let unzip3 (l : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list =\n    List.unzip3 l\n  let splitAt (n : bigint) (l : 'a list) : 'a list * 'a list =\n    List.splitAt (int n) l\n  let unsnoc (l : 'a list) : 'a list * 'a =\n    (List.truncate (List.length l - 1) l, List.last l)\n  let split3 (l : 'a list) (i : bigint) : 'a list * 'a * 'a list =\n    let a, b = List.splitAt (int i) l\n    (a, List.head b, List.tail b)\n  let bool_of_compare (f : 'a -> 'a -> bigint) (x : 'a) (y : 'a) : bool =\n    f x y > 0I\n  let compare_of_bool (r : 'a -> 'a -> bool) (x : 'a) (y : 'a) : bigint =\n    if r x y then 1I elif x = y then 0I else -1I\n  let sortWith (f : 'a -> 'a -> bigint) (l : 'a list) : 'a list =\n    List.sortWith (fun x y -> int (f x y)) l\n  let subset (l : 'a list) (r : 'a list) : bool =\n    List.forall (fun x -> List.contains x r) l\n  let list_unref (l : 'a list) : 'a list = l\n  let list_ref (l : 'a list) : 'a list = l\n  let list_refb (l : 'a list) : 'a list = l\n\nmodule FStar_IO =\n  let private w (s : string) : unit =\n    Console.Out.Write s\n    Console.Out.Flush ()\n\n  let print_newline (_ : unit) : unit = w \"\\n\"\n  let print_string (s : string) : unit = w s\n  let debug_print_string (s : string) : bool = w s; false\n\n  let private hex (v : uint64) : string = \"0x\" + v.ToString \"x\"\n  let private hexpad (n : int) (v : uint64) : string =\n    \"0x\" + v.ToString(\"x\").PadLeft(n, '0')\n  let private decpad (n : int) (v : uint64) : string =\n    v.ToString().PadLeft(n, '0')\n\n  let print_uint8 (v : uint8) : unit = w (hex (uint64 v))\n  let print_uint16 (v : uint16) : unit = w (hex (uint64 v))\n  let print_uint32 (v : uint32) : unit = w (hex (uint64 v))\n  let print_uint64 (v : uint64) : unit = w (hex v)\n\n  let print_uint8_dec (v : uint8) : unit = w (string v)\n  let print_uint16_dec (v : uint16) : unit = w (string v)\n  let print_uint32_dec (v : uint32) : unit = w (string v)\n  let print_uint64_dec (v : uint64) : unit = w (string v)\n\n  let print_uint8_hex_pad (v : uint8) : unit = w (hexpad 2 (uint64 v))\n  let print_uint16_hex_pad (v : uint16) : unit = w (hexpad 4 (uint64 v))\n  let print_uint32_hex_pad (v : uint32) : unit = w (hexpad 8 (uint64 v))\n  let print_uint64_hex_pad (v : uint64) : unit = w (hexpad 16 v)\n\n  let print_uint8_dec_pad (v : uint8) : unit = w (decpad 3 (uint64 v))\n  let print_uint16_dec_pad (v : uint16) : unit = w (decpad 5 (uint64 v))\n  let print_uint32_dec_pad (v : uint32) : unit = w (decpad 10 (uint64 v))\n  let print_uint64_dec_pad (v : uint64) : unit = w (decpad 20 v)\n"
let target_framework : Prims.string= "net10.0"
let project_source (stem : Prims.string) (exe : Prims.bool) : Prims.string=
  Prims.strcat
    "<!-- Generated by F* Custard extraction. Do not edit. -->\n<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <OutputType>"
    (Prims.strcat (if exe then "Exe" else "Library")
       (Prims.strcat "</OutputType>\n    <TargetFramework>"
          (Prims.strcat target_framework
             (Prims.strcat
                "</TargetFramework>\n    <Nullable>disable</Nullable>\n    <InvariantGlobalization>true</InvariantGlobalization>\n    <SatelliteResourceLanguages>en</SatelliteResourceLanguages>\n    <GenerateDocumentationFile>false</GenerateDocumentationFile>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"FStarCustard.fs\" />\n    <Compile Include=\""
                (Prims.strcat stem ".fs\" />\n  </ItemGroup>\n</Project>\n")))))
let project_files (stem : Prims.string) (p : FStarC_Custard_Syntax.program) :
  (Prims.string * Prims.string) Prims.list=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = entrypoints p in
          match uu___4 with | hd::tl -> true | uu___5 -> false in
        project_source stem uu___3 in
      ((Prims.strcat stem ".fsproj"), uu___2) in
    [uu___1] in
  ("FStarCustard.fs", runtime_source) :: uu___
