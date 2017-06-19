open Prims
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Ref_sort
  | Term_sort
  | Fuel_sort
  | Array of (sort* sort)
  | Arrow of (sort* sort)
  | Sort of Prims.string
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____21 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____26 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____31 -> false
let uu___is_Ref_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____36 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____41 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____46 -> false
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____54 -> false
let __proj__Array__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____76 -> false
let __proj__Arrow__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____96 -> false
let __proj__Sort__item___0: sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0
let rec strSort: sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Ref_sort  -> "Ref"
    | Fuel_sort  -> "Fuel"
    | Array (s1,s2) ->
        let uu____111 = strSort s1 in
        let uu____112 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____111 uu____112
    | Arrow (s1,s2) ->
        let uu____115 = strSort s1 in
        let uu____116 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____115 uu____116
    | Sort s -> s
type op =
  | TrueOp
  | FalseOp
  | Not
  | And
  | Or
  | Imp
  | Iff
  | Eq
  | LT
  | LTE
  | GT
  | GTE
  | Add
  | Sub
  | Div
  | Mul
  | Minus
  | Mod
  | ITE
  | Var of Prims.string
let uu___is_TrueOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____126 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____131 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____136 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____141 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____146 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____151 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____156 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____161 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____166 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____171 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____176 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____181 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____186 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____191 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____196 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____201 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____206 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____211 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____216 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____222 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____235 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____240 -> false
type term' =
  | Integer of Prims.string
  | BoundV of Prims.int
  | FreeV of (Prims.string* sort)
  | App of (op* term Prims.list)
  | Quant of (qop* term Prims.list Prims.list* Prims.int option* sort
  Prims.list* term)
  | Let of (term Prims.list* term)
  | Labeled of (term* Prims.string* FStar_Range.range)
  | LblPos of (term* Prims.string)
and term =
  {
  tm: term';
  freevars: (Prims.string* sort) Prims.list FStar_Syntax_Syntax.memo;
  rng: FStar_Range.range;}
let uu___is_Integer: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____317 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____331 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____347 -> false
let __proj__FreeV__item___0: term' -> (Prims.string* sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____370 -> false
let __proj__App__item___0: term' -> (op* term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____402 -> false
let __proj__Quant__item___0:
  term' ->
    (qop* term Prims.list Prims.list* Prims.int option* sort Prims.list*
      term)
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____446 -> false
let __proj__Let__item___0: term' -> (term Prims.list* term) =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____472 -> false
let __proj__Labeled__item___0:
  term' -> (term* Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____497 -> false
let __proj__LblPos__item___0: term' -> (term* Prims.string) =
  fun projectee  -> match projectee with | LblPos _0 -> _0
type pat = term
type fv = (Prims.string* sort)
type fvs = (Prims.string* sort) Prims.list
type caption = Prims.string option
type binders = (Prims.string* sort) Prims.list
type constructor_field = (Prims.string* sort* Prims.bool)
type constructor_t =
  (Prims.string* constructor_field Prims.list* sort* Prims.int* Prims.bool)
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____573 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____587 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____601 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term;
  assumption_caption: caption;
  assumption_name: Prims.string;
  assumption_fact_ids: fact_db_id Prims.list;}
type decl =
  | DefPrelude
  | DeclFun of (Prims.string* sort Prims.list* sort* caption)
  | DefineFun of (Prims.string* sort Prims.list* sort* term* caption)
  | Assume of assumption
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | RetainAssumptions of Prims.string Prims.list
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string* Prims.string)
  | GetStatistics
  | GetReasonUnknown
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____699 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____710 -> false
let __proj__DeclFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____745 -> false
let __proj__DefineFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* term* caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____777 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____791 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____805 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____819 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____834 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____850 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____855 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____860 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____865 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____873 -> false
let __proj__SetOption__item___0: decl -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____892 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____897 -> false
type decls_t = decl Prims.list
type error_label = (fv* Prims.string* FStar_Range.range)
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool = fun x  -> fun y  -> (fst x) = (fst y)
let fv_sort x = snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____941 -> false
let freevar_sort: term -> sort =
  fun uu___86_947  ->
    match uu___86_947 with
    | { tm = FreeV x; freevars = uu____949; rng = uu____950;_} -> fv_sort x
    | uu____957 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___87_961  ->
    match uu___87_961 with
    | { tm = FreeV fv; freevars = uu____963; rng = uu____964;_} -> fv
    | uu____971 -> failwith "impossible"
let rec freevars: term -> (Prims.string* sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____982 -> []
    | BoundV uu____985 -> []
    | FreeV fv -> [fv]
    | App (uu____995,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1001,uu____1002,uu____1003,uu____1004,t1) -> freevars t1
    | Labeled (t1,uu____1015,uu____1016) -> freevars t1
    | LblPos (t1,uu____1018) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1029 = FStar_ST.read t.freevars in
    match uu____1029 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____1052 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1052 in
        (FStar_ST.write t.freevars (Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___88_1065  ->
    match uu___88_1065 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___89_1069  ->
    match uu___89_1069 with
    | TrueOp  -> "true"
    | FalseOp  -> "false"
    | Not  -> "not"
    | And  -> "and"
    | Or  -> "or"
    | Imp  -> "implies"
    | Iff  -> "iff"
    | Eq  -> "="
    | LT  -> "<"
    | LTE  -> "<="
    | GT  -> ">"
    | GTE  -> ">="
    | Add  -> "+"
    | Sub  -> "-"
    | Div  -> "div"
    | Mul  -> "*"
    | Minus  -> "-"
    | Mod  -> "mod"
    | ITE  -> "ite"
    | Var s -> s
let weightToSmt: Prims.int option -> Prims.string =
  fun uu___90_1075  ->
    match uu___90_1075 with
    | None  -> ""
    | Some i ->
        let uu____1078 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1078
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1086 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1086
    | FreeV x ->
        let uu____1090 =
          let uu____1091 = strSort (snd x) in Prims.strcat ":" uu____1091 in
        Prims.strcat (fst x) uu____1090
    | App (op,tms) ->
        let uu____1096 =
          let uu____1097 =
            let uu____1098 =
              let uu____1099 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1099 (FStar_String.concat " ") in
            Prims.strcat uu____1098 ")" in
          Prims.strcat (op_to_string op) uu____1097 in
        Prims.strcat "(" uu____1096
    | Labeled (t1,r1,r2) ->
        let uu____1105 = hash_of_term t1 in
        let uu____1106 =
          let uu____1107 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1107 in
        Prims.strcat uu____1105 uu____1106
    | LblPos (t1,r) ->
        let uu____1110 =
          let uu____1111 = hash_of_term t1 in
          Prims.strcat uu____1111
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1110
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1125 =
          let uu____1126 =
            let uu____1127 =
              let uu____1128 =
                let uu____1129 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1129 (FStar_String.concat " ") in
              let uu____1132 =
                let uu____1133 =
                  let uu____1134 = hash_of_term body in
                  let uu____1135 =
                    let uu____1136 =
                      let uu____1137 = weightToSmt wopt in
                      let uu____1138 =
                        let uu____1139 =
                          let uu____1140 =
                            let uu____1141 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1149 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1149
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1141
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1140 "))" in
                        Prims.strcat " " uu____1139 in
                      Prims.strcat uu____1137 uu____1138 in
                    Prims.strcat " " uu____1136 in
                  Prims.strcat uu____1134 uu____1135 in
                Prims.strcat ")(! " uu____1133 in
              Prims.strcat uu____1128 uu____1132 in
            Prims.strcat " (" uu____1127 in
          Prims.strcat (qop_to_string qop) uu____1126 in
        Prims.strcat "(" uu____1125
    | Let (es,body) ->
        let uu____1157 =
          let uu____1158 =
            let uu____1159 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1159 (FStar_String.concat " ") in
          let uu____1162 =
            let uu____1163 =
              let uu____1164 = hash_of_term body in
              Prims.strcat uu____1164 ")" in
            Prims.strcat ") " uu____1163 in
          Prims.strcat uu____1158 uu____1162 in
        Prims.strcat "(let (" uu____1157
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1174 = FStar_Util.mk_ref None in
      { tm = t; freevars = uu____1174; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1207 =
        let uu____1208 = FStar_Util.ensure_decimal i in Integer uu____1208 in
      mk uu____1207 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1217 = FStar_Util.string_of_int i in mkInteger uu____1217 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV: (Prims.string* sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r
let mkApp': (op* term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r
let mkApp: (Prims.string* term Prims.list) -> FStar_Range.range -> term =
  fun uu____1261  ->
    fun r  -> match uu____1261 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1279) -> mkFalse r
      | App (FalseOp ,uu____1282) -> mkTrue r
      | uu____1285 -> mkApp' (Not, [t]) r
let mkAnd: (term* term) -> FStar_Range.range -> term =
  fun uu____1295  ->
    fun r  ->
      match uu____1295 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1301),uu____1302) -> t2
           | (uu____1305,App (TrueOp ,uu____1306)) -> t1
           | (App (FalseOp ,uu____1309),uu____1310) -> mkFalse r
           | (uu____1313,App (FalseOp ,uu____1314)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1324,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1330) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1334 -> mkApp' (And, [t1; t2]) r)
let mkOr: (term* term) -> FStar_Range.range -> term =
  fun uu____1346  ->
    fun r  ->
      match uu____1346 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1352),uu____1353) -> mkTrue r
           | (uu____1356,App (TrueOp ,uu____1357)) -> mkTrue r
           | (App (FalseOp ,uu____1360),uu____1361) -> t2
           | (uu____1364,App (FalseOp ,uu____1365)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1375,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1381) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1385 -> mkApp' (Or, [t1; t2]) r)
let mkImp: (term* term) -> FStar_Range.range -> term =
  fun uu____1397  ->
    fun r  ->
      match uu____1397 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1403,App (TrueOp ,uu____1404)) -> mkTrue r
           | (App (FalseOp ,uu____1407),uu____1408) -> mkTrue r
           | (App (TrueOp ,uu____1411),uu____1412) -> t2
           | (uu____1415,App (Imp ,t1'::t2'::[])) ->
               let uu____1419 =
                 let uu____1423 =
                   let uu____1425 = mkAnd (t1, t1') r in [uu____1425; t2'] in
                 (Imp, uu____1423) in
               mkApp' uu____1419 r
           | uu____1427 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op: op -> (term* term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1443  ->
      fun r  -> match uu____1443 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
let mkMinus: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r
let mkIff: (term* term) -> FStar_Range.range -> term = mk_bin_op Iff
let mkEq: (term* term) -> FStar_Range.range -> term = mk_bin_op Eq
let mkLT: (term* term) -> FStar_Range.range -> term = mk_bin_op LT
let mkLTE: (term* term) -> FStar_Range.range -> term = mk_bin_op LTE
let mkGT: (term* term) -> FStar_Range.range -> term = mk_bin_op GT
let mkGTE: (term* term) -> FStar_Range.range -> term = mk_bin_op GTE
let mkAdd: (term* term) -> FStar_Range.range -> term = mk_bin_op Add
let mkSub: (term* term) -> FStar_Range.range -> term = mk_bin_op Sub
let mkDiv: (term* term) -> FStar_Range.range -> term = mk_bin_op Div
let mkMul: (term* term) -> FStar_Range.range -> term = mk_bin_op Mul
let mkMod: (term* term) -> FStar_Range.range -> term = mk_bin_op Mod
let mkITE: (term* term* term) -> FStar_Range.range -> term =
  fun uu____1556  ->
    fun r  ->
      match uu____1556 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1564) -> t2
           | App (FalseOp ,uu____1567) -> t3
           | uu____1570 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1571),App (TrueOp ,uu____1572)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1577),uu____1578) ->
                    let uu____1581 =
                      let uu____1584 = mkNot t1 t1.rng in (uu____1584, t3) in
                    mkImp uu____1581 r
                | (uu____1585,App (TrueOp ,uu____1586)) -> mkImp (t1, t2) r
                | (uu____1589,uu____1590) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop* term Prims.list Prims.list* Prims.int option* sort Prims.list* term)
    -> FStar_Range.range -> term
  =
  fun uu____1622  ->
    fun r  ->
      match uu____1622 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1651) -> body
             | uu____1654 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet: (term Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1668  ->
    fun r  ->
      match uu____1668 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1701 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1701 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1718 = FStar_ST.read t1.freevars in
        match uu____1718 with
        | Some [] -> t1
        | uu____1734 ->
            (match t1.tm with
             | Integer uu____1739 -> t1
             | BoundV uu____1740 -> t1
             | FreeV x ->
                 let uu____1744 = index_of x in
                 (match uu____1744 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1751 =
                   let uu____1755 = FStar_List.map (aux ix) tms in
                   (op, uu____1755) in
                 mkApp' uu____1751 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1761 =
                   let uu____1762 =
                     let uu____1766 = aux ix t2 in (uu____1766, r1, r2) in
                   Labeled uu____1762 in
                 mk uu____1761 t2.rng
             | LblPos (t2,r) ->
                 let uu____1769 =
                   let uu____1770 =
                     let uu____1773 = aux ix t2 in (uu____1773, r) in
                   LblPos uu____1770 in
                 mk uu____1769 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1790 =
                   let uu____1800 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1813 = aux (ix + n1) body in
                   (qop, uu____1800, wopt, vars, uu____1813) in
                 mkQuant uu____1790 t1.rng
             | Let (es,body) ->
                 let uu____1826 =
                   FStar_List.fold_left
                     (fun uu____1833  ->
                        fun e  ->
                          match uu____1833 with
                          | (ix1,l) ->
                              let uu____1845 =
                                let uu____1847 = aux ix1 e in uu____1847 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1845))
                     (ix, []) es in
                 (match uu____1826 with
                  | (ix1,es_rev) ->
                      let uu____1854 =
                        let uu____1858 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1858) in
                      mkLet uu____1854 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____1882 -> t1
        | FreeV uu____1883 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1896 =
              let uu____1900 = FStar_List.map (aux shift) tms2 in
              (op, uu____1900) in
            mkApp' uu____1896 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1906 =
              let uu____1907 =
                let uu____1911 = aux shift t2 in (uu____1911, r1, r2) in
              Labeled uu____1907 in
            mk uu____1906 t2.rng
        | LblPos (t2,r) ->
            let uu____1914 =
              let uu____1915 =
                let uu____1918 = aux shift t2 in (uu____1918, r) in
              LblPos uu____1915 in
            mk uu____1914 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1940 =
              let uu____1950 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____1959 = aux shift1 body in
              (qop, uu____1950, wopt, vars, uu____1959) in
            mkQuant uu____1940 t1.rng
        | Let (es,body) ->
            let uu____1968 =
              FStar_List.fold_left
                (fun uu____1975  ->
                   fun e  ->
                     match uu____1975 with
                     | (ix,es1) ->
                         let uu____1987 =
                           let uu____1989 = aux shift e in uu____1989 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____1987))
                (shift, []) es in
            (match uu____1968 with
             | (shift1,es_rev) ->
                 let uu____1996 =
                   let uu____2000 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____2000) in
                 mkLet uu____1996 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____2014 = abstr [fv] t in inst [s] uu____2014
let mkQuant':
  (qop* term Prims.list Prims.list* Prims.int option* fv Prims.list* term) ->
    FStar_Range.range -> term
  =
  fun uu____2029  ->
    match uu____2029 with
    | (qop,pats,wopt,vars,body) ->
        let uu____2054 =
          let uu____2064 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____2073 = FStar_List.map fv_sort vars in
          let uu____2077 = abstr vars body in
          (qop, uu____2064, wopt, uu____2073, uu____2077) in
        mkQuant uu____2054
let mkForall'':
  (pat Prims.list Prims.list* Prims.int option* sort Prims.list* term) ->
    FStar_Range.range -> term
  =
  fun uu____2096  ->
    fun r  ->
      match uu____2096 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list* Prims.int option* fvs* term) ->
    FStar_Range.range -> term
  =
  fun uu____2135  ->
    fun r  ->
      match uu____2135 with
      | (pats,wopt,vars,body) ->
          let uu____2154 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____2154 r
let mkForall:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____2171  ->
    fun r  ->
      match uu____2171 with
      | (pats,vars,body) ->
          let uu____2185 = mkQuant' (Forall, pats, None, vars, body) in
          uu____2185 r
let mkExists:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____2202  ->
    fun r  ->
      match uu____2202 with
      | (pats,vars,body) ->
          let uu____2216 = mkQuant' (Exists, pats, None, vars, body) in
          uu____2216 r
let mkLet': ((fv* term) Prims.list* term) -> FStar_Range.range -> term =
  fun uu____2233  ->
    fun r  ->
      match uu____2233 with
      | (bindings,body) ->
          let uu____2248 = FStar_List.split bindings in
          (match uu____2248 with
           | (vars,es) ->
               let uu____2259 =
                 let uu____2263 = abstr vars body in (es, uu____2263) in
               mkLet uu____2259 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string* (Prims.string* sort) Prims.list* sort* term* caption) ->
    decl
  =
  fun uu____2276  ->
    match uu____2276 with
    | (nm,vars,s,tm,c) ->
        let uu____2296 =
          let uu____2303 = FStar_List.map fv_sort vars in
          let uu____2307 = abstr vars tm in
          (nm, uu____2303, s, uu____2307, c) in
        DefineFun uu____2296
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2313 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2313
let fresh_token: (Prims.string* sort) -> Prims.int -> decl =
  fun uu____2322  ->
    fun id  ->
      match uu____2322 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2330 =
              let uu____2331 =
                let uu____2334 = mkInteger' id norng in
                let uu____2335 =
                  let uu____2336 =
                    let uu____2340 = constr_id_of_sort sort in
                    let uu____2341 =
                      let uu____2343 = mkApp (tok_name, []) norng in
                      [uu____2343] in
                    (uu____2340, uu____2341) in
                  mkApp uu____2336 norng in
                (uu____2334, uu____2335) in
              mkEq uu____2331 norng in
            {
              assumption_term = uu____2330;
              assumption_caption = (Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            } in
          Assume a
let fresh_constructor:
  (Prims.string* sort Prims.list* sort* Prims.int) -> decl =
  fun uu____2354  ->
    match uu____2354 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2373 =
                      let uu____2376 =
                        let uu____2377 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2377 in
                      (uu____2376, s) in
                    mkFreeV uu____2373 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2383 =
            let uu____2387 = constr_id_of_sort sort in (uu____2387, [capp]) in
          mkApp uu____2383 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2391 =
            let uu____2392 =
              let uu____2398 =
                let uu____2399 =
                  let uu____2402 = mkInteger id1 norng in
                  (uu____2402, cid_app) in
                mkEq uu____2399 norng in
              ([[capp]], bvar_names, uu____2398) in
            mkForall uu____2392 norng in
          {
            assumption_term = uu____2391;
            assumption_caption = (Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string* constructor_field Prims.list* sort) -> decl Prims.list =
  fun uu____2415  ->
    match uu____2415 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2432 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2432 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2452 = let uu____2455 = bvar_name i in (uu____2455, s) in
          mkFreeV uu____2452 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2464  ->
                    match uu____2464 with
                    | (uu____2468,s,uu____2470) ->
                        let uu____2471 = bvar i s in uu____2471 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2478 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2489  ->
                    match uu____2489 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2504 =
                              let uu____2505 =
                                let uu____2511 =
                                  let uu____2512 =
                                    let uu____2515 =
                                      let uu____2516 = bvar i s in
                                      uu____2516 norng in
                                    (cproj_app, uu____2515) in
                                  mkEq uu____2512 norng in
                                ([[capp]], bvar_names, uu____2511) in
                              mkForall uu____2505 norng in
                            {
                              assumption_term = uu____2504;
                              assumption_caption =
                                (Some "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2478 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2531  ->
    match uu____2531 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2547  ->
                  match uu____2547 with
                  | (uu____2551,sort1,uu____2553) -> sort1)) in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2566 =
              let uu____2569 =
                let uu____2570 =
                  let uu____2574 = constr_id_of_sort sort in
                  (uu____2574, [xx]) in
                mkApp uu____2570 norng in
              let uu____2576 =
                let uu____2577 = FStar_Util.string_of_int id in
                mkInteger uu____2577 norng in
              (uu____2569, uu____2576) in
            mkEq uu____2566 norng in
          let uu____2578 =
            let uu____2586 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2609  ->
                        match uu____2609 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2626 = mkApp (proj, [xx]) norng in
                              (uu____2626, [])
                            else
                              (let fi =
                                 let uu____2637 =
                                   let uu____2638 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2638 in
                                 (uu____2637, s) in
                               let uu____2639 = mkFreeV fi norng in
                               (uu____2639, [fi])))) in
            FStar_All.pipe_right uu____2586 FStar_List.split in
          match uu____2578 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2682 =
                  let uu____2685 = mkApp (name, proj_terms) norng in
                  (xx, uu____2685) in
                mkEq uu____2682 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2690 -> mkExists ([], ex_vars1, disc_inv_body) norng in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (Some "Discriminator definition")) in
              def in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else [] in
        let uu____2713 =
          let uu____2715 =
            let uu____2716 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2716 in
          uu____2715 :: cdecl :: cid :: projs in
        let uu____2717 =
          let uu____2719 =
            let uu____2721 =
              let uu____2722 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2722 in
            [uu____2721] in
          FStar_List.append [disc] uu____2719 in
        FStar_List.append uu____2713 uu____2717
let name_binders_inner:
  Prims.string option ->
    (Prims.string* sort) Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string* sort) Prims.list* Prims.string Prims.list*
            Prims.int)
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____2756 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2779  ->
                    fun s  ->
                      match uu____2779 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2807 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1 in
                          let nm =
                            let uu____2811 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2811 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____2819 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2819 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2756 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string* sort) Prims.list* Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2862 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts in
    match uu____2862 with
    | (names1,binders,n1) -> ((FStar_List.rev names1), binders)
let termToSmt: Prims.string -> term -> Prims.string =
  fun enclosing_name  ->
    fun t  ->
      let next_qid =
        let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
        fun depth  ->
          let n1 = FStar_ST.read ctr in
          FStar_Util.incr ctr;
          if n1 = (Prims.parse_int "0")
          then enclosing_name
          else
            (let uu____2918 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____2918) in
      let remove_guard_free pats =
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun ps  ->
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun tm  ->
                        match tm.tm with
                        | App
                            (Var
                             "Prims.guard_free",{ tm = BoundV uu____2940;
                                                  freevars = uu____2941;
                                                  rng = uu____2942;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____2950 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____2986 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____2986 FStar_Pervasives.fst
        | FreeV x -> fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____2996 =
              let uu____2997 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____2997 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2996
        | Labeled (t2,uu____3001,uu____3002) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____3005 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____3005 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____3020 = name_binders_inner None names1 n1 sorts in
            (match uu____3020 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____3048 ->
                       let uu____3051 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____3059 =
                                   let uu____3060 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____3063 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____3063)
                                       pats2 in
                                   FStar_String.concat " " uu____3060 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____3059)) in
                       FStar_All.pipe_right uu____3051
                         (FStar_String.concat "\n") in
                 let uu____3065 =
                   let uu____3067 =
                     let uu____3069 =
                       let uu____3071 = aux1 n2 names2 body in
                       let uu____3072 =
                         let uu____3074 = weightToSmt wopt in
                         [uu____3074; pats_str; qid] in
                       uu____3071 :: uu____3072 in
                     binders1 :: uu____3069 in
                   (qop_to_string qop) :: uu____3067 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____3065)
        | Let (es,body) ->
            let uu____3079 =
              FStar_List.fold_left
                (fun uu____3094  ->
                   fun e  ->
                     match uu____3094 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____3122 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____3122 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____3130 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____3130 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____3079 with
             | (names2,binders,n2) ->
                 let uu____3148 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____3148)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____3155 = FStar_Range.string_of_range t1.rng in
          let uu____3156 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____3155
            uu____3156 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string: Prims.string option -> Prims.string =
  fun uu___91_3162  ->
    match uu___91_3162 with
    | None  -> ""
    | Some c ->
        let uu____3165 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____3174 -> (hd1, "...") in
        (match uu____3165 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____3191 = FStar_Options.log_queries () in
          if uu____3191
          then
            let uu____3192 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___92_3194  ->
                   match uu___92_3194 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____3192
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____3208 = caption_to_string c in
          let uu____3209 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____3208 f
            (FStar_String.concat " " l) uu____3209
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____3217 = name_macro_binders arg_sorts in
          (match uu____3217 with
           | (names1,binders) ->
               let body1 =
                 let uu____3235 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____3235 body in
               let uu____3242 = caption_to_string c in
               let uu____3243 = strSort retsort in
               let uu____3244 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3242
                 f (FStar_String.concat " " binders) uu____3243 uu____3244)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___93_3255  ->
                    match uu___93_3255 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____3260 = FStar_Options.log_queries () in
            if uu____3260
            then
              let uu____3261 =
                let uu____3262 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____3262 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3261
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3266 = caption_to_string a.assumption_caption in
          let uu____3267 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3266 fids
            uu____3267 n1
      | Eval t ->
          let uu____3269 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3269
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3271 -> ""
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
      | GetStatistics  ->
          "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
      | GetReasonUnknown  ->
          "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and mkPrelude: Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, (Prims.parse_int "0"), true);
      ("Tm_type", [], Term_sort, (Prims.parse_int "2"), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.parse_int "3"), false);
      ("Tm_uvar", [("Tm_uvar_fst", Int_sort, true)], Term_sort,
        (Prims.parse_int "5"), true);
      ("Tm_unit", [], Term_sort, (Prims.parse_int "6"), true);
      ("BoxInt", [("BoxInt_proj_0", Int_sort, true)], Term_sort,
        (Prims.parse_int "7"), true);
      ("BoxBool", [("BoxBool_proj_0", Bool_sort, true)], Term_sort,
        (Prims.parse_int "8"), true);
      ("BoxString", [("BoxString_proj_0", String_sort, true)], Term_sort,
        (Prims.parse_int "9"), true);
      ("BoxRef", [("BoxRef_proj_0", Ref_sort, true)], Term_sort,
        (Prims.parse_int "10"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.parse_int "11"), true)] in
    let bcons =
      let uu____3475 =
        let uu____3477 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3477
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3475 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3507 =
        let uu____3511 = let uu____3513 = mkInteger' i norng in [uu____3513] in
        ("Tm_uvar", uu____3511) in
      mkApp uu____3507 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        match t.tm with
        | App (Var v',t1::[]) when
            (v1 = v') && (FStar_Options.smtencoding_elim_box ()) -> t1
        | uu____3531 -> mkApp (u, [t]) t.rng
let boxInt: term -> term =
  fun t  -> maybe_elim_box "BoxInt" "BoxInt_proj_0" t
let unboxInt: term -> term =
  fun t  -> maybe_elim_box "BoxInt_proj_0" "BoxInt" t
let boxBool: term -> term =
  fun t  -> maybe_elim_box "BoxBool" "BoxBool_proj_0" t
let unboxBool: term -> term =
  fun t  -> maybe_elim_box "BoxBool_proj_0" "BoxBool" t
let boxString: term -> term =
  fun t  -> maybe_elim_box "BoxString" "BoxString_proj_0" t
let unboxString: term -> term =
  fun t  -> maybe_elim_box "BoxString_proj_0" "BoxString" t
let boxRef: term -> term =
  fun t  -> maybe_elim_box "BoxRef" "BoxRef_proj_0" t
let unboxRef: term -> term =
  fun t  -> maybe_elim_box "BoxRef_proj_0" "BoxRef" t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | uu____3573 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3582 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3592::t1::t2::[]);
                       freevars = uu____3595; rng = uu____3596;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3603::t1::t2::[]);
                       freevars = uu____3606; rng = uu____3607;_}::[])
        -> let uu____3614 = mkEq (t1, t2) norng in mkNot uu____3614 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3617; rng = uu____3618;_}::[])
        ->
        let uu____3625 =
          let uu____3628 = unboxInt t1 in
          let uu____3629 = unboxInt t2 in (uu____3628, uu____3629) in
        mkLTE uu____3625 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3632; rng = uu____3633;_}::[])
        ->
        let uu____3640 =
          let uu____3643 = unboxInt t1 in
          let uu____3644 = unboxInt t2 in (uu____3643, uu____3644) in
        mkLT uu____3640 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3647; rng = uu____3648;_}::[])
        ->
        let uu____3655 =
          let uu____3658 = unboxInt t1 in
          let uu____3659 = unboxInt t2 in (uu____3658, uu____3659) in
        mkGTE uu____3655 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3662; rng = uu____3663;_}::[])
        ->
        let uu____3670 =
          let uu____3673 = unboxInt t1 in
          let uu____3674 = unboxInt t2 in (uu____3673, uu____3674) in
        mkGT uu____3670 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3677; rng = uu____3678;_}::[])
        ->
        let uu____3685 =
          let uu____3688 = unboxBool t1 in
          let uu____3689 = unboxBool t2 in (uu____3688, uu____3689) in
        mkAnd uu____3685 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3692; rng = uu____3693;_}::[])
        ->
        let uu____3700 =
          let uu____3703 = unboxBool t1 in
          let uu____3704 = unboxBool t2 in (uu____3703, uu____3704) in
        mkOr uu____3700 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3706; rng = uu____3707;_}::[])
        -> let uu____3714 = unboxBool t1 in mkNot uu____3714 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___94_3717 = unboxBool t1 in
        {
          tm = (uu___94_3717.tm);
          freevars = (uu___94_3717.freevars);
          rng = (t.rng)
        }
    | uu____3720 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3757 = FStar_Options.unthrottle_inductives () in
        if uu____3757
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel: term option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | None  -> mk_HasType v1 t
        | Some f1 -> mk_HasTypeFuel f1 v1 t
let mk_NoHoist: term -> term -> term =
  fun dummy  -> fun b  -> mkApp ("NoHoist", [dummy; b]) b.rng
let mk_Destruct: term -> FStar_Range.range -> term =
  fun v1  -> mkApp ("Destruct", [v1])
let mk_Rank: term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x])
let mk_tester: Prims.string -> term -> term =
  fun n1  -> fun t  -> mkApp ((Prims.strcat "is-" n1), [t]) t.rng
let mk_ApplyTF: term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng
let mk_ApplyTT: term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r
let mk_String_const: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3839 =
        let uu____3843 = let uu____3845 = mkInteger' i norng in [uu____3845] in
        ("FString_const", uu____3843) in
      mkApp uu____3839 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3859 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3859 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3880 =
         let uu____3884 =
           let uu____3886 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3886] in
         ("SFuel", uu____3884) in
       mkApp uu____3880 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term option -> term option -> FStar_Range.range -> term option =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (Some p11,Some p21) ->
            let uu____3912 = mkAnd (p11, p21) r in Some uu____3912
        | (Some p,None ) -> Some p
        | (None ,Some p) -> Some p
        | (None ,None ) -> None
let mk_and_opt_l: term option Prims.list -> FStar_Range.range -> term option
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3950 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3950
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3963 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3963
let mk_haseq: term -> term =
  fun t  ->
    let uu____3970 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____3970
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3984 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____3984
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (fst fv)
    | App (op,l) ->
        let uu____3992 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3992
    | Labeled (t1,r1,r2) ->
        let uu____3996 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3996
    | LblPos (t1,s) ->
        let uu____3999 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3999
    | Quant (qop,l,uu____4002,uu____4003,t1) ->
        let uu____4013 = print_smt_term_list_list l in
        let uu____4014 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4013
          uu____4014
    | Let (es,body) ->
        let uu____4019 = print_smt_term_list es in
        let uu____4020 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____4019 uu____4020
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____4023 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____4023 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4033 =
             let uu____4034 =
               let uu____4035 = print_smt_term_list l1 in
               Prims.strcat uu____4035 " ] " in
             Prims.strcat "; [ " uu____4034 in
           Prims.strcat s uu____4033) "" l