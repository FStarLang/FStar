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
    match projectee with | Bool_sort  -> true | uu____20 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____24 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____28 -> false
let uu___is_Ref_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____32 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____36 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____40 -> false
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____47 -> false
let __proj__Array__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____67 -> false
let __proj__Arrow__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____85 -> false
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
        let uu____98 = strSort s1 in
        let uu____99 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____98 uu____99
    | Arrow (s1,s2) ->
        let uu____102 = strSort s1 in
        let uu____103 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____102 uu____103
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
    match projectee with | TrueOp  -> true | uu____112 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____116 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____120 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____124 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____128 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____132 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____136 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____140 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____144 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____148 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____152 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____156 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____160 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____164 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____168 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____172 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____176 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____180 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____184 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____189 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____200 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____204 -> false
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
    match projectee with | Integer _0 -> true | uu____280 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____292 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____306 -> false
let __proj__FreeV__item___0: term' -> (Prims.string* sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____327 -> false
let __proj__App__item___0: term' -> (op* term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____357 -> false
let __proj__Quant__item___0:
  term' ->
    (qop* term Prims.list Prims.list* Prims.int option* sort Prims.list*
      term)
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____399 -> false
let __proj__Let__item___0: term' -> (term Prims.list* term) =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____423 -> false
let __proj__Labeled__item___0:
  term' -> (term* Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____446 -> false
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
    match projectee with | Name _0 -> true | uu____517 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____529 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____541 -> false
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
    match projectee with | DefPrelude  -> true | uu____633 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____643 -> false
let __proj__DeclFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____676 -> false
let __proj__DefineFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* term* caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____706 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____718 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____730 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____742 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____755 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____769 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____773 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____777 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____781 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____788 -> false
let __proj__SetOption__item___0: decl -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____805 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____809 -> false
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
      | uu____846 -> false
let freevar_sort: term -> sort =
  fun uu___86_851  ->
    match uu___86_851 with
    | { tm = FreeV x; freevars = uu____853; rng = uu____854;_} -> fv_sort x
    | uu____861 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___87_864  ->
    match uu___87_864 with
    | { tm = FreeV fv; freevars = uu____866; rng = uu____867;_} -> fv
    | uu____874 -> failwith "impossible"
let rec freevars: term -> (Prims.string* sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____884 -> []
    | BoundV uu____887 -> []
    | FreeV fv -> [fv]
    | App (uu____897,tms) -> FStar_List.collect freevars tms
    | Quant (uu____903,uu____904,uu____905,uu____906,t1) -> freevars t1
    | Labeled (t1,uu____917,uu____918) -> freevars t1
    | LblPos (t1,uu____920) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____930 = FStar_ST.read t.freevars in
    match uu____930 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____953 = freevars t in
          FStar_Util.remove_dups fv_eq uu____953 in
        (FStar_ST.write t.freevars (Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___88_965  ->
    match uu___88_965 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___89_968  ->
    match uu___89_968 with
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
  fun uu___90_973  ->
    match uu___90_973 with
    | None  -> ""
    | Some i ->
        let uu____976 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____976
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____984 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____984
    | FreeV x ->
        let uu____988 =
          let uu____989 = strSort (snd x) in Prims.strcat ":" uu____989 in
        Prims.strcat (fst x) uu____988
    | App (op,tms) ->
        let uu____994 =
          let uu____995 =
            let uu____996 =
              let uu____997 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____997 (FStar_String.concat " ") in
            Prims.strcat uu____996 ")" in
          Prims.strcat (op_to_string op) uu____995 in
        Prims.strcat "(" uu____994
    | Labeled (t1,r1,r2) ->
        let uu____1003 = hash_of_term t1 in
        let uu____1004 =
          let uu____1005 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1005 in
        Prims.strcat uu____1003 uu____1004
    | LblPos (t1,r) ->
        let uu____1008 =
          let uu____1009 = hash_of_term t1 in
          Prims.strcat uu____1009
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1008
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1023 =
          let uu____1024 =
            let uu____1025 =
              let uu____1026 =
                let uu____1027 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1027 (FStar_String.concat " ") in
              let uu____1030 =
                let uu____1031 =
                  let uu____1032 = hash_of_term body in
                  let uu____1033 =
                    let uu____1034 =
                      let uu____1035 = weightToSmt wopt in
                      let uu____1036 =
                        let uu____1037 =
                          let uu____1038 =
                            let uu____1039 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1047 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1047
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1039
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1038 "))" in
                        Prims.strcat " " uu____1037 in
                      Prims.strcat uu____1035 uu____1036 in
                    Prims.strcat " " uu____1034 in
                  Prims.strcat uu____1032 uu____1033 in
                Prims.strcat ")(! " uu____1031 in
              Prims.strcat uu____1026 uu____1030 in
            Prims.strcat " (" uu____1025 in
          Prims.strcat (qop_to_string qop) uu____1024 in
        Prims.strcat "(" uu____1023
    | Let (es,body) ->
        let uu____1055 =
          let uu____1056 =
            let uu____1057 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1057 (FStar_String.concat " ") in
          let uu____1060 =
            let uu____1061 =
              let uu____1062 = hash_of_term body in
              Prims.strcat uu____1062 ")" in
            Prims.strcat ") " uu____1061 in
          Prims.strcat uu____1056 uu____1060 in
        Prims.strcat "(let (" uu____1055
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1070 = FStar_Util.mk_ref None in
      { tm = t; freevars = uu____1070; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1099 =
        let uu____1100 = FStar_Util.ensure_decimal i in Integer uu____1100 in
      mk uu____1099 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1107 = FStar_Util.string_of_int i in mkInteger uu____1107 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV: (Prims.string* sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r
let mkApp': (op* term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r
let mkApp: (Prims.string* term Prims.list) -> FStar_Range.range -> term =
  fun uu____1143  ->
    fun r  -> match uu____1143 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1159) -> mkFalse r
      | App (FalseOp ,uu____1162) -> mkTrue r
      | uu____1165 -> mkApp' (Not, [t]) r
let mkAnd: (term* term) -> FStar_Range.range -> term =
  fun uu____1173  ->
    fun r  ->
      match uu____1173 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1179),uu____1180) -> t2
           | (uu____1183,App (TrueOp ,uu____1184)) -> t1
           | (App (FalseOp ,uu____1187),uu____1188) -> mkFalse r
           | (uu____1191,App (FalseOp ,uu____1192)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1202,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1208) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1212 -> mkApp' (And, [t1; t2]) r)
let mkOr: (term* term) -> FStar_Range.range -> term =
  fun uu____1222  ->
    fun r  ->
      match uu____1222 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1228),uu____1229) -> mkTrue r
           | (uu____1232,App (TrueOp ,uu____1233)) -> mkTrue r
           | (App (FalseOp ,uu____1236),uu____1237) -> t2
           | (uu____1240,App (FalseOp ,uu____1241)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1251,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1257) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1261 -> mkApp' (Or, [t1; t2]) r)
let mkImp: (term* term) -> FStar_Range.range -> term =
  fun uu____1271  ->
    fun r  ->
      match uu____1271 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1277,App (TrueOp ,uu____1278)) -> mkTrue r
           | (App (FalseOp ,uu____1281),uu____1282) -> mkTrue r
           | (App (TrueOp ,uu____1285),uu____1286) -> t2
           | (uu____1289,App (Imp ,t1'::t2'::[])) ->
               let uu____1293 =
                 let uu____1297 =
                   let uu____1299 = mkAnd (t1, t1') r in [uu____1299; t2'] in
                 (Imp, uu____1297) in
               mkApp' uu____1293 r
           | uu____1301 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op: op -> (term* term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1314  ->
      fun r  -> match uu____1314 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
  fun uu____1401  ->
    fun r  ->
      match uu____1401 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1409) -> t2
           | App (FalseOp ,uu____1412) -> t3
           | uu____1415 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1416),App (TrueOp ,uu____1417)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1422),uu____1423) ->
                    let uu____1426 =
                      let uu____1429 = mkNot t1 t1.rng in (uu____1429, t3) in
                    mkImp uu____1426 r
                | (uu____1430,App (TrueOp ,uu____1431)) -> mkImp (t1, t2) r
                | (uu____1434,uu____1435) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____1463  ->
    fun r  ->
      match uu____1463 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1492) -> body
             | uu____1495 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet: (term Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1507  ->
    fun r  ->
      match uu____1507 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1538 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1538 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1555 = FStar_ST.read t1.freevars in
        match uu____1555 with
        | Some [] -> t1
        | uu____1571 ->
            (match t1.tm with
             | Integer uu____1576 -> t1
             | BoundV uu____1577 -> t1
             | FreeV x ->
                 let uu____1581 = index_of x in
                 (match uu____1581 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1588 =
                   let uu____1592 = FStar_List.map (aux ix) tms in
                   (op, uu____1592) in
                 mkApp' uu____1588 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1598 =
                   let uu____1599 =
                     let uu____1603 = aux ix t2 in (uu____1603, r1, r2) in
                   Labeled uu____1599 in
                 mk uu____1598 t2.rng
             | LblPos (t2,r) ->
                 let uu____1606 =
                   let uu____1607 =
                     let uu____1610 = aux ix t2 in (uu____1610, r) in
                   LblPos uu____1607 in
                 mk uu____1606 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1627 =
                   let uu____1637 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1650 = aux (ix + n1) body in
                   (qop, uu____1637, wopt, vars, uu____1650) in
                 mkQuant uu____1627 t1.rng
             | Let (es,body) ->
                 let uu____1663 =
                   FStar_List.fold_left
                     (fun uu____1670  ->
                        fun e  ->
                          match uu____1670 with
                          | (ix1,l) ->
                              let uu____1682 =
                                let uu____1684 = aux ix1 e in uu____1684 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1682))
                     (ix, []) es in
                 (match uu____1663 with
                  | (ix1,es_rev) ->
                      let uu____1691 =
                        let uu____1695 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1695) in
                      mkLet uu____1691 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____1717 -> t1
        | FreeV uu____1718 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1731 =
              let uu____1735 = FStar_List.map (aux shift) tms2 in
              (op, uu____1735) in
            mkApp' uu____1731 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1741 =
              let uu____1742 =
                let uu____1746 = aux shift t2 in (uu____1746, r1, r2) in
              Labeled uu____1742 in
            mk uu____1741 t2.rng
        | LblPos (t2,r) ->
            let uu____1749 =
              let uu____1750 =
                let uu____1753 = aux shift t2 in (uu____1753, r) in
              LblPos uu____1750 in
            mk uu____1749 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1775 =
              let uu____1785 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____1794 = aux shift1 body in
              (qop, uu____1785, wopt, vars, uu____1794) in
            mkQuant uu____1775 t1.rng
        | Let (es,body) ->
            let uu____1803 =
              FStar_List.fold_left
                (fun uu____1810  ->
                   fun e  ->
                     match uu____1810 with
                     | (ix,es1) ->
                         let uu____1822 =
                           let uu____1824 = aux shift e in uu____1824 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____1822))
                (shift, []) es in
            (match uu____1803 with
             | (shift1,es_rev) ->
                 let uu____1831 =
                   let uu____1835 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____1835) in
                 mkLet uu____1831 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____1846 = abstr [fv] t in inst [s] uu____1846
let mkQuant':
  (qop* term Prims.list Prims.list* Prims.int option* fv Prims.list* term) ->
    FStar_Range.range -> term
  =
  fun uu____1860  ->
    match uu____1860 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1885 =
          let uu____1895 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____1904 = FStar_List.map fv_sort vars in
          let uu____1908 = abstr vars body in
          (qop, uu____1895, wopt, uu____1904, uu____1908) in
        mkQuant uu____1885
let mkForall'':
  (pat Prims.list Prims.list* Prims.int option* sort Prims.list* term) ->
    FStar_Range.range -> term
  =
  fun uu____1925  ->
    fun r  ->
      match uu____1925 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list* Prims.int option* fvs* term) ->
    FStar_Range.range -> term
  =
  fun uu____1962  ->
    fun r  ->
      match uu____1962 with
      | (pats,wopt,vars,body) ->
          let uu____1981 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____1981 r
let mkForall:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1996  ->
    fun r  ->
      match uu____1996 with
      | (pats,vars,body) ->
          let uu____2010 = mkQuant' (Forall, pats, None, vars, body) in
          uu____2010 r
let mkExists:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____2025  ->
    fun r  ->
      match uu____2025 with
      | (pats,vars,body) ->
          let uu____2039 = mkQuant' (Exists, pats, None, vars, body) in
          uu____2039 r
let mkLet': ((fv* term) Prims.list* term) -> FStar_Range.range -> term =
  fun uu____2054  ->
    fun r  ->
      match uu____2054 with
      | (bindings,body) ->
          let uu____2069 = FStar_List.split bindings in
          (match uu____2069 with
           | (vars,es) ->
               let uu____2080 =
                 let uu____2084 = abstr vars body in (es, uu____2084) in
               mkLet uu____2080 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string* (Prims.string* sort) Prims.list* sort* term* caption) ->
    decl
  =
  fun uu____2096  ->
    match uu____2096 with
    | (nm,vars,s,tm,c) ->
        let uu____2116 =
          let uu____2123 = FStar_List.map fv_sort vars in
          let uu____2127 = abstr vars tm in
          (nm, uu____2123, s, uu____2127, c) in
        DefineFun uu____2116
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2132 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2132
let fresh_token: (Prims.string* sort) -> Prims.int -> decl =
  fun uu____2139  ->
    fun id  ->
      match uu____2139 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2147 =
              let uu____2148 =
                let uu____2151 = mkInteger' id norng in
                let uu____2152 =
                  let uu____2153 =
                    let uu____2157 = constr_id_of_sort sort in
                    let uu____2158 =
                      let uu____2160 = mkApp (tok_name, []) norng in
                      [uu____2160] in
                    (uu____2157, uu____2158) in
                  mkApp uu____2153 norng in
                (uu____2151, uu____2152) in
              mkEq uu____2148 norng in
            {
              assumption_term = uu____2147;
              assumption_caption = (Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            } in
          Assume a
let fresh_constructor:
  (Prims.string* sort Prims.list* sort* Prims.int) -> decl =
  fun uu____2170  ->
    match uu____2170 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2189 =
                      let uu____2192 =
                        let uu____2193 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2193 in
                      (uu____2192, s) in
                    mkFreeV uu____2189 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2199 =
            let uu____2203 = constr_id_of_sort sort in (uu____2203, [capp]) in
          mkApp uu____2199 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2207 =
            let uu____2208 =
              let uu____2214 =
                let uu____2215 =
                  let uu____2218 = mkInteger id1 norng in
                  (uu____2218, cid_app) in
                mkEq uu____2215 norng in
              ([[capp]], bvar_names, uu____2214) in
            mkForall uu____2208 norng in
          {
            assumption_term = uu____2207;
            assumption_caption = (Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string* constructor_field Prims.list* sort) -> decl Prims.list =
  fun uu____2230  ->
    match uu____2230 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2247 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2247 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2267 = let uu____2270 = bvar_name i in (uu____2270, s) in
          mkFreeV uu____2267 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2279  ->
                    match uu____2279 with
                    | (uu____2283,s,uu____2285) ->
                        let uu____2286 = bvar i s in uu____2286 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2293 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2304  ->
                    match uu____2304 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2319 =
                              let uu____2320 =
                                let uu____2326 =
                                  let uu____2327 =
                                    let uu____2330 =
                                      let uu____2331 = bvar i s in
                                      uu____2331 norng in
                                    (cproj_app, uu____2330) in
                                  mkEq uu____2327 norng in
                                ([[capp]], bvar_names, uu____2326) in
                              mkForall uu____2320 norng in
                            {
                              assumption_term = uu____2319;
                              assumption_caption =
                                (Some "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2293 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2345  ->
    match uu____2345 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2361  ->
                  match uu____2361 with
                  | (uu____2365,sort1,uu____2367) -> sort1)) in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2380 =
              let uu____2383 =
                let uu____2384 =
                  let uu____2388 = constr_id_of_sort sort in
                  (uu____2388, [xx]) in
                mkApp uu____2384 norng in
              let uu____2390 =
                let uu____2391 = FStar_Util.string_of_int id in
                mkInteger uu____2391 norng in
              (uu____2383, uu____2390) in
            mkEq uu____2380 norng in
          let uu____2392 =
            let uu____2400 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2423  ->
                        match uu____2423 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2440 = mkApp (proj, [xx]) norng in
                              (uu____2440, [])
                            else
                              (let fi =
                                 let uu____2451 =
                                   let uu____2452 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2452 in
                                 (uu____2451, s) in
                               let uu____2453 = mkFreeV fi norng in
                               (uu____2453, [fi])))) in
            FStar_All.pipe_right uu____2400 FStar_List.split in
          match uu____2392 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2496 =
                  let uu____2499 = mkApp (name, proj_terms) norng in
                  (xx, uu____2499) in
                mkEq uu____2496 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2504 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____2527 =
          let uu____2529 =
            let uu____2530 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2530 in
          uu____2529 :: cdecl :: cid :: projs in
        let uu____2531 =
          let uu____2533 =
            let uu____2535 =
              let uu____2536 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2536 in
            [uu____2535] in
          FStar_List.append [disc] uu____2533 in
        FStar_List.append uu____2527 uu____2531
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
          let uu____2566 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2589  ->
                    fun s  ->
                      match uu____2589 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2617 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1 in
                          let nm =
                            let uu____2621 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2621 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____2629 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2629 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2566 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string* sort) Prims.list* Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2671 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts in
    match uu____2671 with
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
            (let uu____2725 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____2725) in
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
                             "Prims.guard_free",{ tm = BoundV uu____2747;
                                                  freevars = uu____2748;
                                                  rng = uu____2749;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____2757 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____2793 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____2793 FStar_Pervasives.fst
        | FreeV x -> fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____2803 =
              let uu____2804 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____2804 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2803
        | Labeled (t2,uu____2808,uu____2809) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____2812 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____2812 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____2827 = name_binders_inner None names1 n1 sorts in
            (match uu____2827 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____2855 ->
                       let uu____2858 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____2866 =
                                   let uu____2867 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____2870 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____2870)
                                       pats2 in
                                   FStar_String.concat " " uu____2867 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____2866)) in
                       FStar_All.pipe_right uu____2858
                         (FStar_String.concat "\n") in
                 let uu____2872 =
                   let uu____2874 =
                     let uu____2876 =
                       let uu____2878 = aux1 n2 names2 body in
                       let uu____2879 =
                         let uu____2881 = weightToSmt wopt in
                         [uu____2881; pats_str; qid] in
                       uu____2878 :: uu____2879 in
                     binders1 :: uu____2876 in
                   (qop_to_string qop) :: uu____2874 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____2872)
        | Let (es,body) ->
            let uu____2886 =
              FStar_List.fold_left
                (fun uu____2901  ->
                   fun e  ->
                     match uu____2901 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____2929 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____2929 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____2937 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____2937 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____2886 with
             | (names2,binders,n2) ->
                 let uu____2955 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____2955)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____2962 = FStar_Range.string_of_range t1.rng in
          let uu____2963 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2962
            uu____2963 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string: Prims.string option -> Prims.string =
  fun uu___91_2968  ->
    match uu___91_2968 with
    | None  -> ""
    | Some c ->
        let uu____2971 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2980 -> (hd1, "...") in
        (match uu____2971 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2997 = FStar_Options.log_queries () in
          if uu____2997
          then
            let uu____2998 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___92_3000  ->
                   match uu___92_3000 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____2998
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____3014 = caption_to_string c in
          let uu____3015 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____3014 f
            (FStar_String.concat " " l) uu____3015
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____3023 = name_macro_binders arg_sorts in
          (match uu____3023 with
           | (names1,binders) ->
               let body1 =
                 let uu____3041 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____3041 body in
               let uu____3048 = caption_to_string c in
               let uu____3049 = strSort retsort in
               let uu____3050 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3048
                 f (FStar_String.concat " " binders) uu____3049 uu____3050)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___93_3061  ->
                    match uu___93_3061 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____3066 = FStar_Options.log_queries () in
            if uu____3066
            then
              let uu____3067 =
                let uu____3068 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____3068 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3067
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3072 = caption_to_string a.assumption_caption in
          let uu____3073 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3072 fids
            uu____3073 n1
      | Eval t ->
          let uu____3075 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3075
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3077 -> ""
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
      let uu____3281 =
        let uu____3283 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3283
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3281 (FStar_String.concat "\n") in
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
      let uu____3308 =
        let uu____3312 = let uu____3314 = mkInteger' i norng in [uu____3314] in
        ("Tm_uvar", uu____3312) in
      mkApp uu____3308 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        match t.tm with
        | App (Var v',t1::[]) when
            (v1 = v') && (FStar_Options.smtencoding_elim_box ()) -> t1
        | uu____3329 -> mkApp (u, [t]) t.rng
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
      | uu____3361 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3368 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3376::t1::t2::[]);
                       freevars = uu____3379; rng = uu____3380;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3387::t1::t2::[]);
                       freevars = uu____3390; rng = uu____3391;_}::[])
        -> let uu____3398 = mkEq (t1, t2) norng in mkNot uu____3398 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3401; rng = uu____3402;_}::[])
        ->
        let uu____3409 =
          let uu____3412 = unboxInt t1 in
          let uu____3413 = unboxInt t2 in (uu____3412, uu____3413) in
        mkLTE uu____3409 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3416; rng = uu____3417;_}::[])
        ->
        let uu____3424 =
          let uu____3427 = unboxInt t1 in
          let uu____3428 = unboxInt t2 in (uu____3427, uu____3428) in
        mkLT uu____3424 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3431; rng = uu____3432;_}::[])
        ->
        let uu____3439 =
          let uu____3442 = unboxInt t1 in
          let uu____3443 = unboxInt t2 in (uu____3442, uu____3443) in
        mkGTE uu____3439 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3446; rng = uu____3447;_}::[])
        ->
        let uu____3454 =
          let uu____3457 = unboxInt t1 in
          let uu____3458 = unboxInt t2 in (uu____3457, uu____3458) in
        mkGT uu____3454 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3461; rng = uu____3462;_}::[])
        ->
        let uu____3469 =
          let uu____3472 = unboxBool t1 in
          let uu____3473 = unboxBool t2 in (uu____3472, uu____3473) in
        mkAnd uu____3469 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3476; rng = uu____3477;_}::[])
        ->
        let uu____3484 =
          let uu____3487 = unboxBool t1 in
          let uu____3488 = unboxBool t2 in (uu____3487, uu____3488) in
        mkOr uu____3484 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3490; rng = uu____3491;_}::[])
        -> let uu____3498 = unboxBool t1 in mkNot uu____3498 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___94_3501 = unboxBool t1 in
        {
          tm = (uu___94_3501.tm);
          freevars = (uu___94_3501.freevars);
          rng = (t.rng)
        }
    | uu____3504 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3533 = FStar_Options.unthrottle_inductives () in
        if uu____3533
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
      let uu____3597 =
        let uu____3601 = let uu____3603 = mkInteger' i norng in [uu____3603] in
        ("FString_const", uu____3601) in
      mkApp uu____3597 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3614 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3614 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3631 =
         let uu____3635 =
           let uu____3637 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3637] in
         ("SFuel", uu____3635) in
       mkApp uu____3631 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term option -> term option -> FStar_Range.range -> term option =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (Some p11,Some p21) ->
            let uu____3660 = mkAnd (p11, p21) r in Some uu____3660
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
      let uu____3694 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3694
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3705 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3705
let mk_haseq: term -> term =
  fun t  ->
    let uu____3711 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____3711
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3725 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____3725
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (fst fv)
    | App (op,l) ->
        let uu____3733 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3733
    | Labeled (t1,r1,r2) ->
        let uu____3737 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3737
    | LblPos (t1,s) ->
        let uu____3740 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3740
    | Quant (qop,l,uu____3743,uu____3744,t1) ->
        let uu____3754 = print_smt_term_list_list l in
        let uu____3755 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3754
          uu____3755
    | Let (es,body) ->
        let uu____3760 = print_smt_term_list es in
        let uu____3761 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____3760 uu____3761
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____3764 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____3764 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3774 =
             let uu____3775 =
               let uu____3776 = print_smt_term_list l1 in
               Prims.strcat uu____3776 " ] " in
             Prims.strcat "; [ " uu____3775 in
           Prims.strcat s uu____3774) "" l