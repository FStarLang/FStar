open Prims
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Ref_sort
  | Term_sort
  | Fuel_sort
  | Array of (sort,sort) FStar_Pervasives_Native.tuple2
  | Arrow of (sort,sort) FStar_Pervasives_Native.tuple2
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
let __proj__Array__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____76 -> false
let __proj__Arrow__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
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
  | FreeV of (Prims.string,sort) FStar_Pervasives_Native.tuple2
  | App of (op,term Prims.list) FStar_Pervasives_Native.tuple2
  | Quant of
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
  sort Prims.list,term) FStar_Pervasives_Native.tuple5
  | Let of (term Prims.list,term) FStar_Pervasives_Native.tuple2
  | Labeled of (term,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | LblPos of (term,Prims.string) FStar_Pervasives_Native.tuple2
and term =
  {
  tm: term';
  freevars:
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo;
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
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____370 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____402 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____446 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____472 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____497 -> false
let __proj__LblPos__item___0:
  term' -> (term,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LblPos _0 -> _0
let __proj__Mkterm__item__tm: term -> term' =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__tm
let __proj__Mkterm__item__freevars:
  term ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo
  =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__freevars
let __proj__Mkterm__item__rng: term -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { tm = __fname__tm; freevars = __fname__freevars; rng = __fname__rng;_}
        -> __fname__rng
type pat = term
type fv = (Prims.string,sort) FStar_Pervasives_Native.tuple2
type fvs = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
type caption = Prims.string FStar_Pervasives_Native.option
type binders = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
type constructor_field =
  (Prims.string,sort,Prims.bool) FStar_Pervasives_Native.tuple3
type constructor_t =
  (Prims.string,constructor_field Prims.list,sort,Prims.int,Prims.bool)
    FStar_Pervasives_Native.tuple5
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____592 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____606 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____620 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term;
  assumption_caption: caption;
  assumption_name: Prims.string;
  assumption_fact_ids: fact_db_id Prims.list;}
let __proj__Mkassumption__item__assumption_term: assumption -> term =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_term
let __proj__Mkassumption__item__assumption_caption: assumption -> caption =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_caption
let __proj__Mkassumption__item__assumption_name: assumption -> Prims.string =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_name
let __proj__Mkassumption__item__assumption_fact_ids:
  assumption -> fact_db_id Prims.list =
  fun projectee  ->
    match projectee with
    | { assumption_term = __fname__assumption_term;
        assumption_caption = __fname__assumption_caption;
        assumption_name = __fname__assumption_name;
        assumption_fact_ids = __fname__assumption_fact_ids;_} ->
        __fname__assumption_fact_ids
type decl =
  | DefPrelude
  | DeclFun of (Prims.string,sort Prims.list,sort,caption)
  FStar_Pervasives_Native.tuple4
  | DefineFun of (Prims.string,sort Prims.list,sort,term,caption)
  FStar_Pervasives_Native.tuple5
  | Assume of assumption
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | RetainAssumptions of Prims.string Prims.list
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  | GetStatistics
  | GetReasonUnknown
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____734 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____745 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____780 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____812 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____826 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____840 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____854 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____869 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____885 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____890 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____895 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____900 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____908 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____927 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____932 -> false
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
let fv_sort x = FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____976 -> false
let freevar_sort: term -> sort =
  fun uu___87_982  ->
    match uu___87_982 with
    | { tm = FreeV x; freevars = uu____984; rng = uu____985;_} -> fv_sort x
    | uu____992 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___88_996  ->
    match uu___88_996 with
    | { tm = FreeV fv; freevars = uu____998; rng = uu____999;_} -> fv
    | uu____1006 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1017 -> []
    | BoundV uu____1020 -> []
    | FreeV fv -> [fv]
    | App (uu____1030,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1036,uu____1037,uu____1038,uu____1039,t1) -> freevars t1
    | Labeled (t1,uu____1050,uu____1051) -> freevars t1
    | LblPos (t1,uu____1053) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1064 = FStar_ST.read t.freevars in
    match uu____1064 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1087 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1087 in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___89_1100  ->
    match uu___89_1100 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___90_1104  ->
    match uu___90_1104 with
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
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___91_1110  ->
    match uu___91_1110 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1113 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1113
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1121 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1121
    | FreeV x ->
        let uu____1125 =
          let uu____1126 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1126 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1125
    | App (op,tms) ->
        let uu____1131 =
          let uu____1132 =
            let uu____1133 =
              let uu____1134 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1134 (FStar_String.concat " ") in
            Prims.strcat uu____1133 ")" in
          Prims.strcat (op_to_string op) uu____1132 in
        Prims.strcat "(" uu____1131
    | Labeled (t1,r1,r2) ->
        let uu____1140 = hash_of_term t1 in
        let uu____1141 =
          let uu____1142 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1142 in
        Prims.strcat uu____1140 uu____1141
    | LblPos (t1,r) ->
        let uu____1145 =
          let uu____1146 = hash_of_term t1 in
          Prims.strcat uu____1146
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1145
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1160 =
          let uu____1161 =
            let uu____1162 =
              let uu____1163 =
                let uu____1164 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1164 (FStar_String.concat " ") in
              let uu____1167 =
                let uu____1168 =
                  let uu____1169 = hash_of_term body in
                  let uu____1170 =
                    let uu____1171 =
                      let uu____1172 = weightToSmt wopt in
                      let uu____1173 =
                        let uu____1174 =
                          let uu____1175 =
                            let uu____1176 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1186 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1186
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1176
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1175 "))" in
                        Prims.strcat " " uu____1174 in
                      Prims.strcat uu____1172 uu____1173 in
                    Prims.strcat " " uu____1171 in
                  Prims.strcat uu____1169 uu____1170 in
                Prims.strcat ")(! " uu____1168 in
              Prims.strcat uu____1163 uu____1167 in
            Prims.strcat " (" uu____1162 in
          Prims.strcat (qop_to_string qop) uu____1161 in
        Prims.strcat "(" uu____1160
    | Let (es,body) ->
        let uu____1194 =
          let uu____1195 =
            let uu____1196 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1196 (FStar_String.concat " ") in
          let uu____1199 =
            let uu____1200 =
              let uu____1201 = hash_of_term body in
              Prims.strcat uu____1201 ")" in
            Prims.strcat ") " uu____1200 in
          Prims.strcat uu____1195 uu____1199 in
        Prims.strcat "(let (" uu____1194
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1211 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1211; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1244 =
        let uu____1245 = FStar_Util.ensure_decimal i in Integer uu____1245 in
      mk uu____1244 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1254 = FStar_Util.string_of_int i in mkInteger uu____1254 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun x  -> fun r  -> mk (FreeV x) r
let mkApp':
  (op,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun f  -> fun r  -> mk (App f) r
let mkApp:
  (Prims.string,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____1298  ->
    fun r  -> match uu____1298 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1316) -> mkFalse r
      | App (FalseOp ,uu____1319) -> mkTrue r
      | uu____1322 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1332  ->
    fun r  ->
      match uu____1332 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1338),uu____1339) -> t2
           | (uu____1342,App (TrueOp ,uu____1343)) -> t1
           | (App (FalseOp ,uu____1346),uu____1347) -> mkFalse r
           | (uu____1350,App (FalseOp ,uu____1351)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1361,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1367) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1371 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1383  ->
    fun r  ->
      match uu____1383 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1389),uu____1390) -> mkTrue r
           | (uu____1393,App (TrueOp ,uu____1394)) -> mkTrue r
           | (App (FalseOp ,uu____1397),uu____1398) -> t2
           | (uu____1401,App (FalseOp ,uu____1402)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1412,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1418) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1422 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1434  ->
    fun r  ->
      match uu____1434 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1440,App (TrueOp ,uu____1441)) -> mkTrue r
           | (App (FalseOp ,uu____1444),uu____1445) -> mkTrue r
           | (App (TrueOp ,uu____1448),uu____1449) -> t2
           | (uu____1452,App (Imp ,t1'::t2'::[])) ->
               let uu____1456 =
                 let uu____1460 =
                   let uu____1462 = mkAnd (t1, t1') r in [uu____1462; t2'] in
                 (Imp, uu____1460) in
               mkApp' uu____1456 r
           | uu____1464 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____1480  ->
      fun r  -> match uu____1480 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
let mkMinus: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Eq
let mkLT:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LT
let mkLTE:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LTE
let mkGT:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GT
let mkGTE:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GTE
let mkAdd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Add
let mkSub:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Sub
let mkDiv:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Div
let mkMul:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mul
let mkMod:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mod
let mkITE:
  (term,term,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____1593  ->
    fun r  ->
      match uu____1593 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1601) -> t2
           | App (FalseOp ,uu____1604) -> t3
           | uu____1607 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1608),App (TrueOp ,uu____1609)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1614),uu____1615) ->
                    let uu____1618 =
                      let uu____1621 = mkNot t1 t1.rng in (uu____1621, t3) in
                    mkImp uu____1618 r
                | (uu____1622,App (TrueOp ,uu____1623)) -> mkImp (t1, t2) r
                | (uu____1626,uu____1627) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____1661  ->
    fun r  ->
      match uu____1661 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1690) -> body
             | uu____1693 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____1707  ->
    fun r  ->
      match uu____1707 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1740 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1740 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1757 = FStar_ST.read t1.freevars in
        match uu____1757 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____1773 ->
            (match t1.tm with
             | Integer uu____1778 -> t1
             | BoundV uu____1779 -> t1
             | FreeV x ->
                 let uu____1783 = index_of x in
                 (match uu____1783 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1790 =
                   let uu____1794 = FStar_List.map (aux ix) tms in
                   (op, uu____1794) in
                 mkApp' uu____1790 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1800 =
                   let uu____1801 =
                     let uu____1805 = aux ix t2 in (uu____1805, r1, r2) in
                   Labeled uu____1801 in
                 mk uu____1800 t2.rng
             | LblPos (t2,r) ->
                 let uu____1808 =
                   let uu____1809 =
                     let uu____1812 = aux ix t2 in (uu____1812, r) in
                   LblPos uu____1809 in
                 mk uu____1808 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1829 =
                   let uu____1839 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1852 = aux (ix + n1) body in
                   (qop, uu____1839, wopt, vars, uu____1852) in
                 mkQuant uu____1829 t1.rng
             | Let (es,body) ->
                 let uu____1865 =
                   FStar_List.fold_left
                     (fun uu____1877  ->
                        fun e  ->
                          match uu____1877 with
                          | (ix1,l) ->
                              let uu____1889 =
                                let uu____1891 = aux ix1 e in uu____1891 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1889))
                     (ix, []) es in
                 (match uu____1865 with
                  | (ix1,es_rev) ->
                      let uu____1898 =
                        let uu____1902 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1902) in
                      mkLet uu____1898 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____1926 -> t1
        | FreeV uu____1927 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1940 =
              let uu____1944 = FStar_List.map (aux shift) tms2 in
              (op, uu____1944) in
            mkApp' uu____1940 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1950 =
              let uu____1951 =
                let uu____1955 = aux shift t2 in (uu____1955, r1, r2) in
              Labeled uu____1951 in
            mk uu____1950 t2.rng
        | LblPos (t2,r) ->
            let uu____1958 =
              let uu____1959 =
                let uu____1962 = aux shift t2 in (uu____1962, r) in
              LblPos uu____1959 in
            mk uu____1958 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1984 =
              let uu____1994 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____2003 = aux shift1 body in
              (qop, uu____1994, wopt, vars, uu____2003) in
            mkQuant uu____1984 t1.rng
        | Let (es,body) ->
            let uu____2012 =
              FStar_List.fold_left
                (fun uu____2024  ->
                   fun e  ->
                     match uu____2024 with
                     | (ix,es1) ->
                         let uu____2036 =
                           let uu____2038 = aux shift e in uu____2038 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____2036))
                (shift, []) es in
            (match uu____2012 with
             | (shift1,es_rev) ->
                 let uu____2045 =
                   let uu____2049 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____2049) in
                 mkLet uu____2045 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____2063 = abstr [fv] t in inst [s] uu____2063
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____2078  ->
    match uu____2078 with
    | (qop,pats,wopt,vars,body) ->
        let uu____2103 =
          let uu____2113 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____2122 = FStar_List.map fv_sort vars in
          let uu____2126 = abstr vars body in
          (qop, uu____2113, wopt, uu____2122, uu____2126) in
        mkQuant uu____2103
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____2145  ->
    fun r  ->
      match uu____2145 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____2184  ->
    fun r  ->
      match uu____2184 with
      | (pats,wopt,vars,body) ->
          let uu____2203 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____2203 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2220  ->
    fun r  ->
      match uu____2220 with
      | (pats,vars,body) ->
          let uu____2234 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2234 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2251  ->
    fun r  ->
      match uu____2251 with
      | (pats,vars,body) ->
          let uu____2265 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2265 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____2282  ->
    fun r  ->
      match uu____2282 with
      | (bindings,body) ->
          let uu____2297 = FStar_List.split bindings in
          (match uu____2297 with
           | (vars,es) ->
               let uu____2308 =
                 let uu____2312 = abstr vars body in (es, uu____2312) in
               mkLet uu____2308 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____2325  ->
    match uu____2325 with
    | (nm,vars,s,tm,c) ->
        let uu____2345 =
          let uu____2352 = FStar_List.map fv_sort vars in
          let uu____2356 = abstr vars tm in
          (nm, uu____2352, s, uu____2356, c) in
        DefineFun uu____2345
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2362 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2362
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____2371  ->
    fun id  ->
      match uu____2371 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2379 =
              let uu____2380 =
                let uu____2383 = mkInteger' id norng in
                let uu____2384 =
                  let uu____2385 =
                    let uu____2389 = constr_id_of_sort sort in
                    let uu____2390 =
                      let uu____2392 = mkApp (tok_name, []) norng in
                      [uu____2392] in
                    (uu____2389, uu____2390) in
                  mkApp uu____2385 norng in
                (uu____2383, uu____2384) in
              mkEq uu____2380 norng in
            {
              assumption_term = uu____2379;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            } in
          Assume a
let fresh_constructor:
  (Prims.string,sort Prims.list,sort,Prims.int)
    FStar_Pervasives_Native.tuple4 -> decl
  =
  fun uu____2403  ->
    match uu____2403 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2425 =
                      let uu____2428 =
                        let uu____2429 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2429 in
                      (uu____2428, s) in
                    mkFreeV uu____2425 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2435 =
            let uu____2439 = constr_id_of_sort sort in (uu____2439, [capp]) in
          mkApp uu____2435 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2443 =
            let uu____2444 =
              let uu____2450 =
                let uu____2451 =
                  let uu____2454 = mkInteger id1 norng in
                  (uu____2454, cid_app) in
                mkEq uu____2451 norng in
              ([[capp]], bvar_names, uu____2450) in
            mkForall uu____2444 norng in
          {
            assumption_term = uu____2443;
            assumption_caption =
              (FStar_Pervasives_Native.Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string,constructor_field Prims.list,sort)
    FStar_Pervasives_Native.tuple3 -> decl Prims.list
  =
  fun uu____2467  ->
    match uu____2467 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2484 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2484 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2504 = let uu____2507 = bvar_name i in (uu____2507, s) in
          mkFreeV uu____2504 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2522  ->
                    match uu____2522 with
                    | (uu____2526,s,uu____2528) ->
                        let uu____2529 = bvar i s in uu____2529 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2536 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2555  ->
                    match uu____2555 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2570 =
                              let uu____2571 =
                                let uu____2577 =
                                  let uu____2578 =
                                    let uu____2581 =
                                      let uu____2582 = bvar i s in
                                      uu____2582 norng in
                                    (cproj_app, uu____2581) in
                                  mkEq uu____2578 norng in
                                ([[capp]], bvar_names, uu____2577) in
                              mkForall uu____2571 norng in
                            {
                              assumption_term = uu____2570;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2536 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2597  ->
    match uu____2597 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2617  ->
                  match uu____2617 with
                  | (uu____2621,sort1,uu____2623) -> sort1)) in
        let cdecl =
          DeclFun
            (name, field_sorts, sort,
              (FStar_Pervasives_Native.Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2636 =
              let uu____2639 =
                let uu____2640 =
                  let uu____2644 = constr_id_of_sort sort in
                  (uu____2644, [xx]) in
                mkApp uu____2640 norng in
              let uu____2646 =
                let uu____2647 = FStar_Util.string_of_int id in
                mkInteger uu____2647 norng in
              (uu____2639, uu____2646) in
            mkEq uu____2636 norng in
          let uu____2648 =
            let uu____2656 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2685  ->
                        match uu____2685 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2702 = mkApp (proj, [xx]) norng in
                              (uu____2702, [])
                            else
                              (let fi =
                                 let uu____2713 =
                                   let uu____2714 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2714 in
                                 (uu____2713, s) in
                               let uu____2715 = mkFreeV fi norng in
                               (uu____2715, [fi])))) in
            FStar_All.pipe_right uu____2656 FStar_List.split in
          match uu____2648 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2758 =
                  let uu____2761 = mkApp (name, proj_terms) norng in
                  (xx, uu____2761) in
                mkEq uu____2758 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2766 -> mkExists ([], ex_vars1, disc_inv_body) norng in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (FStar_Pervasives_Native.Some "Discriminator definition")) in
              def in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else [] in
        let uu____2789 =
          let uu____2791 =
            let uu____2792 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2792 in
          uu____2791 :: cdecl :: cid :: projs in
        let uu____2793 =
          let uu____2795 =
            let uu____2797 =
              let uu____2798 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2798 in
            [uu____2797] in
          FStar_List.append [disc] uu____2795 in
        FStar_List.append uu____2789 uu____2793
let name_binders_inner:
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
            Prims.string Prims.list,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____2832 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2865  ->
                    fun s  ->
                      match uu____2865 with
                      | (names1,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2893 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____2897 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2897 in
                          let names2 = (nm, s) :: names1 in
                          let b =
                            let uu____2905 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2905 in
                          (names2, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2832 with
          | (names1,binders,n1) -> (names1, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____2948 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____2948 with
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
            (let uu____3004 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____3004) in
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
                             "Prims.guard_free",{ tm = BoundV uu____3031;
                                                  freevars = uu____3032;
                                                  rng = uu____3033;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____3041 -> tm)))) in
      let rec aux' depth n1 names1 t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____3077 = FStar_List.nth names1 i in
            FStar_All.pipe_right uu____3077 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____3087 =
              let uu____3088 = FStar_List.map (aux1 n1 names1) tms in
              FStar_All.pipe_right uu____3088 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3087
        | Labeled (t2,uu____3092,uu____3093) -> aux1 n1 names1 t2
        | LblPos (t2,s) ->
            let uu____3096 = aux1 n1 names1 t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____3096 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____3111 =
              name_binders_inner FStar_Pervasives_Native.None names1 n1 sorts in
            (match uu____3111 with
             | (names2,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____3139 ->
                       let uu____3142 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____3152 =
                                   let uu____3153 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____3158 = aux1 n2 names2 p in
                                          FStar_Util.format1 "%s" uu____3158)
                                       pats2 in
                                   FStar_String.concat " " uu____3153 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____3152)) in
                       FStar_All.pipe_right uu____3142
                         (FStar_String.concat "\n") in
                 let uu____3160 =
                   let uu____3162 =
                     let uu____3164 =
                       let uu____3166 = aux1 n2 names2 body in
                       let uu____3167 =
                         let uu____3169 = weightToSmt wopt in
                         [uu____3169; pats_str; qid] in
                       uu____3166 :: uu____3167 in
                     binders1 :: uu____3164 in
                   (qop_to_string qop) :: uu____3162 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____3160)
        | Let (es,body) ->
            let uu____3174 =
              FStar_List.fold_left
                (fun uu____3197  ->
                   fun e  ->
                     match uu____3197 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____3225 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____3225 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____3233 = aux1 n1 names1 e in
                           FStar_Util.format2 "(%s %s)" nm uu____3233 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names1, [], n1) es in
            (match uu____3174 with
             | (names2,binders,n2) ->
                 let uu____3251 = aux1 n2 names2 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____3251)
      and aux depth n1 names1 t1 =
        let s = aux' depth n1 names1 t1 in
        if t1.rng <> norng
        then
          let uu____3258 = FStar_Range.string_of_range t1.rng in
          let uu____3259 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____3258
            uu____3259 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___92_3265  ->
    match uu___92_3265 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____3268 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____3277 -> (hd1, "...") in
        (match uu____3268 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____3294 = FStar_Options.log_queries () in
          if uu____3294
          then
            let uu____3295 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___93_3298  ->
                   match uu___93_3298 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____3295
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____3312 = caption_to_string c in
          let uu____3313 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____3312 f
            (FStar_String.concat " " l) uu____3313
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____3321 = name_macro_binders arg_sorts in
          (match uu____3321 with
           | (names1,binders) ->
               let body1 =
                 let uu____3339 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names1 in
                 inst uu____3339 body in
               let uu____3347 = caption_to_string c in
               let uu____3348 = strSort retsort in
               let uu____3349 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3347
                 f (FStar_String.concat " " binders) uu____3348 uu____3349)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___94_3362  ->
                    match uu___94_3362 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____3367 = FStar_Options.log_queries () in
            if uu____3367
            then
              let uu____3368 =
                let uu____3369 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____3369 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3368
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3373 = caption_to_string a.assumption_caption in
          let uu____3374 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3373 fids
            uu____3374 n1
      | Eval t ->
          let uu____3376 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3376
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3378 -> ""
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
      let uu____3582 =
        let uu____3584 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3584
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3582 (FStar_String.concat "\n") in
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
      let uu____3614 =
        let uu____3618 = let uu____3620 = mkInteger' i norng in [uu____3620] in
        ("Tm_uvar", uu____3618) in
      mkApp uu____3614 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        match t.tm with
        | App (Var v',t1::[]) when
            (v1 = v') && (FStar_Options.smtencoding_elim_box ()) -> t1
        | uu____3638 -> mkApp (u, [t]) t.rng
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
      | uu____3680 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3689 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3699::t1::t2::[]);
                       freevars = uu____3702; rng = uu____3703;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3710::t1::t2::[]);
                       freevars = uu____3713; rng = uu____3714;_}::[])
        -> let uu____3721 = mkEq (t1, t2) norng in mkNot uu____3721 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3724; rng = uu____3725;_}::[])
        ->
        let uu____3732 =
          let uu____3735 = unboxInt t1 in
          let uu____3736 = unboxInt t2 in (uu____3735, uu____3736) in
        mkLTE uu____3732 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3739; rng = uu____3740;_}::[])
        ->
        let uu____3747 =
          let uu____3750 = unboxInt t1 in
          let uu____3751 = unboxInt t2 in (uu____3750, uu____3751) in
        mkLT uu____3747 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3754; rng = uu____3755;_}::[])
        ->
        let uu____3762 =
          let uu____3765 = unboxInt t1 in
          let uu____3766 = unboxInt t2 in (uu____3765, uu____3766) in
        mkGTE uu____3762 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3769; rng = uu____3770;_}::[])
        ->
        let uu____3777 =
          let uu____3780 = unboxInt t1 in
          let uu____3781 = unboxInt t2 in (uu____3780, uu____3781) in
        mkGT uu____3777 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3784; rng = uu____3785;_}::[])
        ->
        let uu____3792 =
          let uu____3795 = unboxBool t1 in
          let uu____3796 = unboxBool t2 in (uu____3795, uu____3796) in
        mkAnd uu____3792 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3799; rng = uu____3800;_}::[])
        ->
        let uu____3807 =
          let uu____3810 = unboxBool t1 in
          let uu____3811 = unboxBool t2 in (uu____3810, uu____3811) in
        mkOr uu____3807 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3813; rng = uu____3814;_}::[])
        -> let uu____3821 = unboxBool t1 in mkNot uu____3821 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___95_3824 = unboxBool t1 in
        {
          tm = (uu___95_3824.tm);
          freevars = (uu___95_3824.freevars);
          rng = (t.rng)
        }
    | uu____3827 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3864 = FStar_Options.unthrottle_inductives () in
        if uu____3864
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel:
  term FStar_Pervasives_Native.option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | FStar_Pervasives_Native.None  -> mk_HasType v1 t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v1 t
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
      let uu____3946 =
        let uu____3950 = let uu____3952 = mkInteger' i norng in [uu____3952] in
        ("FString_const", uu____3950) in
      mkApp uu____3946 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3966 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3966 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3987 =
         let uu____3991 =
           let uu____3993 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3993] in
         ("SFuel", uu____3991) in
       mkApp uu____3987 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term FStar_Pervasives_Native.option ->
    term FStar_Pervasives_Native.option ->
      FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (FStar_Pervasives_Native.Some p11,FStar_Pervasives_Native.Some p21)
            ->
            let uu____4019 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____4019
        | (FStar_Pervasives_Native.Some p,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some p) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.None
let mk_and_opt_l:
  term FStar_Pervasives_Native.option Prims.list ->
    FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        FStar_Pervasives_Native.None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____4059 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____4059
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____4074 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____4074
let mk_haseq: term -> term =
  fun t  ->
    let uu____4083 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____4083
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____4097 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____4097
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____4105 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____4105
    | Labeled (t1,r1,r2) ->
        let uu____4109 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____4109
    | LblPos (t1,s) ->
        let uu____4112 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____4112
    | Quant (qop,l,uu____4115,uu____4116,t1) ->
        let uu____4126 = print_smt_term_list_list l in
        let uu____4127 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____4126
          uu____4127
    | Let (es,body) ->
        let uu____4132 = print_smt_term_list es in
        let uu____4133 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____4132 uu____4133
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____4136 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____4136 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____4149 =
             let uu____4150 =
               let uu____4151 = print_smt_term_list l1 in
               Prims.strcat uu____4151 " ] " in
             Prims.strcat "; [ " uu____4150 in
           Prims.strcat s uu____4149) "" l