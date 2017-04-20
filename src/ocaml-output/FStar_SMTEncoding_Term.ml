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
    match projectee with | Bool_sort  -> true | uu____17 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____21 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____25 -> false
let uu___is_Ref_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____29 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____33 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____37 -> false
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____44 -> false
let __proj__Array__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____64 -> false
let __proj__Arrow__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____82 -> false
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
        let uu____95 = strSort s1 in
        let uu____96 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____95 uu____96
    | Arrow (s1,s2) ->
        let uu____99 = strSort s1 in
        let uu____100 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____99 uu____100
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
    match projectee with | TrueOp  -> true | uu____108 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____112 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____116 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____120 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____124 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____128 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____132 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____136 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____140 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____144 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____148 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____152 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____156 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____160 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____164 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____168 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____172 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____176 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____180 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____185 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____196 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____200 -> false
type term' =
  | Integer of Prims.string
  | BoundV of Prims.int
  | FreeV of (Prims.string* sort)
  | App of (op* term Prims.list)
  | Quant of (qop* term Prims.list Prims.list* Prims.int Prims.option* sort
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
    match projectee with | Integer _0 -> true | uu____265 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____277 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____291 -> false
let __proj__FreeV__item___0: term' -> (Prims.string* sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____312 -> false
let __proj__App__item___0: term' -> (op* term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____342 -> false
let __proj__Quant__item___0:
  term' ->
    (qop* term Prims.list Prims.list* Prims.int Prims.option* sort
      Prims.list* term)
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____384 -> false
let __proj__Let__item___0: term' -> (term Prims.list* term) =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____408 -> false
let __proj__Labeled__item___0:
  term' -> (term* Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____431 -> false
let __proj__LblPos__item___0: term' -> (term* Prims.string) =
  fun projectee  -> match projectee with | LblPos _0 -> _0
type pat = term
type fv = (Prims.string* sort)
type fvs = (Prims.string* sort) Prims.list
type caption = Prims.string Prims.option
type binders = (Prims.string* sort) Prims.list
type constructor_field = (Prims.string* sort* Prims.bool)
type constructor_t =
  (Prims.string* constructor_field Prims.list* sort* Prims.int* Prims.bool)
type constructors = constructor_t Prims.list
type decl =
  | DefPrelude
  | DeclFun of (Prims.string* sort Prims.list* sort* caption)
  | DefineFun of (Prims.string* sort Prims.list* sort* term* caption)
  | Assume of (term* caption* Prims.string)
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string* Prims.string)
  | PrintStats
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____526 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____536 -> false
let __proj__DeclFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____569 -> false
let __proj__DefineFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* term* caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____602 -> false
let __proj__Assume__item___0: decl -> (term* caption* Prims.string) =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____623 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____635 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____647 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____658 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____662 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____666 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____670 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____677 -> false
let __proj__SetOption__item___0: decl -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_PrintStats: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | PrintStats  -> true | uu____694 -> false
type decls_t = decl Prims.list
type error_label = (fv* Prims.string* FStar_Range.range)
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  -> fun y  -> (Prims.fst x) = (Prims.fst y)
let fv_sort x = Prims.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____731 -> false
let freevar_sort: term -> sort =
  fun uu___85_736  ->
    match uu___85_736 with
    | { tm = FreeV x; freevars = uu____738; rng = uu____739;_} -> fv_sort x
    | uu____746 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___86_749  ->
    match uu___86_749 with
    | { tm = FreeV fv; freevars = uu____751; rng = uu____752;_} -> fv
    | uu____759 -> failwith "impossible"
let rec freevars: term -> (Prims.string* sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____780,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t1)|Labeled (t1,_,_)|LblPos (t1,_) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____807 = FStar_ST.read t.freevars in
    match uu____807 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____830 = freevars t in
          FStar_Util.remove_dups fv_eq uu____830 in
        (FStar_ST.write t.freevars (Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___87_842  ->
    match uu___87_842 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___88_845  ->
    match uu___88_845 with
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
let weightToSmt: Prims.int Prims.option -> Prims.string =
  fun uu___89_850  ->
    match uu___89_850 with
    | None  -> ""
    | Some i ->
        let uu____853 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____853
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____861 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____861
    | FreeV x ->
        let uu____865 =
          let uu____866 = strSort (Prims.snd x) in Prims.strcat ":" uu____866 in
        Prims.strcat (Prims.fst x) uu____865
    | App (op,tms) ->
        let uu____871 =
          let uu____872 =
            let uu____873 =
              let uu____874 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____874 (FStar_String.concat " ") in
            Prims.strcat uu____873 ")" in
          Prims.strcat (op_to_string op) uu____872 in
        Prims.strcat "(" uu____871
    | Labeled (t1,r1,r2) ->
        let uu____880 = hash_of_term t1 in
        let uu____881 =
          let uu____882 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____882 in
        Prims.strcat uu____880 uu____881
    | LblPos (t1,r) ->
        let uu____885 =
          let uu____886 = hash_of_term t1 in
          Prims.strcat uu____886
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____885
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____900 =
          let uu____901 =
            let uu____902 =
              let uu____903 =
                let uu____904 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____904 (FStar_String.concat " ") in
              let uu____907 =
                let uu____908 =
                  let uu____909 = hash_of_term body in
                  let uu____910 =
                    let uu____911 =
                      let uu____912 = weightToSmt wopt in
                      let uu____913 =
                        let uu____914 =
                          let uu____915 =
                            let uu____916 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____924 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____924
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____916
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____915 "))" in
                        Prims.strcat " " uu____914 in
                      Prims.strcat uu____912 uu____913 in
                    Prims.strcat " " uu____911 in
                  Prims.strcat uu____909 uu____910 in
                Prims.strcat ")(! " uu____908 in
              Prims.strcat uu____903 uu____907 in
            Prims.strcat " (" uu____902 in
          Prims.strcat (qop_to_string qop) uu____901 in
        Prims.strcat "(" uu____900
    | Let (es,body) ->
        let uu____932 =
          let uu____933 =
            let uu____934 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____934 (FStar_String.concat " ") in
          let uu____937 =
            let uu____938 =
              let uu____939 = hash_of_term body in Prims.strcat uu____939 ")" in
            Prims.strcat ") " uu____938 in
          Prims.strcat uu____933 uu____937 in
        Prims.strcat "(let (" uu____932
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____947 = FStar_Util.mk_ref None in
      { tm = t; freevars = uu____947; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____976 =
        let uu____977 = FStar_Util.ensure_decimal i in Integer uu____977 in
      mk uu____976 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____984 = FStar_Util.string_of_int i in mkInteger uu____984 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV: (Prims.string* sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r
let mkApp': (op* term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r
let mkApp: (Prims.string* term Prims.list) -> FStar_Range.range -> term =
  fun uu____1020  ->
    fun r  -> match uu____1020 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1036) -> mkFalse r
      | App (FalseOp ,uu____1039) -> mkTrue r
      | uu____1042 -> mkApp' (Not, [t]) r
let mkAnd: (term* term) -> FStar_Range.range -> term =
  fun uu____1050  ->
    fun r  ->
      match uu____1050 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1056),uu____1057) -> t2
           | (uu____1060,App (TrueOp ,uu____1061)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1077,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1083) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1087 -> mkApp' (And, [t1; t2]) r)
let mkOr: (term* term) -> FStar_Range.range -> term =
  fun uu____1097  ->
    fun r  ->
      match uu____1097 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1109),uu____1110) -> t2
           | (uu____1113,App (FalseOp ,uu____1114)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1124,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1130) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1134 -> mkApp' (Or, [t1; t2]) r)
let mkImp: (term* term) -> FStar_Range.range -> term =
  fun uu____1144  ->
    fun r  ->
      match uu____1144 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1156),uu____1157) -> t2
           | (uu____1160,App (Imp ,t1'::t2'::[])) ->
               let uu____1164 =
                 let uu____1168 =
                   let uu____1170 = mkAnd (t1, t1') r in [uu____1170; t2'] in
                 (Imp, uu____1168) in
               mkApp' uu____1164 r
           | uu____1172 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op: op -> (term* term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1185  ->
      fun r  -> match uu____1185 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
  fun uu____1272  ->
    fun r  ->
      match uu____1272 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1280) -> t2
           | App (FalseOp ,uu____1283) -> t3
           | uu____1286 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1287),App (TrueOp ,uu____1288)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1293),uu____1294) ->
                    let uu____1297 =
                      let uu____1300 = mkNot t1 t1.rng in (uu____1300, t3) in
                    mkImp uu____1297 r
                | (uu____1301,App (TrueOp ,uu____1302)) -> mkImp (t1, t2) r
                | (uu____1305,uu____1306) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop* term Prims.list Prims.list* Prims.int Prims.option* sort Prims.list*
    term) -> FStar_Range.range -> term
  =
  fun uu____1334  ->
    fun r  ->
      match uu____1334 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1361) -> body
             | uu____1364 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet: (term Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1376  ->
    fun r  ->
      match uu____1376 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1404 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1404 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1418 = FStar_ST.read t1.freevars in
        match uu____1418 with
        | Some [] -> t1
        | uu____1434 ->
            (match t1.tm with
             | Integer _|BoundV _ -> t1
             | FreeV x ->
                 let uu____1444 = index_of x in
                 (match uu____1444 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1451 =
                   let uu____1455 = FStar_List.map (aux ix) tms in
                   (op, uu____1455) in
                 mkApp' uu____1451 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1461 =
                   let uu____1462 =
                     let uu____1466 = aux ix t2 in (uu____1466, r1, r2) in
                   Labeled uu____1462 in
                 mk uu____1461 t2.rng
             | LblPos (t2,r) ->
                 let uu____1469 =
                   let uu____1470 =
                     let uu____1473 = aux ix t2 in (uu____1473, r) in
                   LblPos uu____1470 in
                 mk uu____1469 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1489 =
                   let uu____1499 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1510 = aux (ix + n1) body in
                   (qop, uu____1499, wopt, vars, uu____1510) in
                 mkQuant uu____1489 t1.rng
             | Let (es,body) ->
                 let uu____1521 =
                   FStar_List.fold_left
                     (fun uu____1528  ->
                        fun e  ->
                          match uu____1528 with
                          | (ix1,l) ->
                              let uu____1540 =
                                let uu____1542 = aux ix1 e in uu____1542 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1540))
                     (ix, []) es in
                 (match uu____1521 with
                  | (ix1,es_rev) ->
                      let uu____1549 =
                        let uu____1553 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1553) in
                      mkLet uu____1549 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer _|FreeV _ -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1584 =
              let uu____1588 = FStar_List.map (aux shift) tms2 in
              (op, uu____1588) in
            mkApp' uu____1584 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1594 =
              let uu____1595 =
                let uu____1599 = aux shift t2 in (uu____1599, r1, r2) in
              Labeled uu____1595 in
            mk uu____1594 t2.rng
        | LblPos (t2,r) ->
            let uu____1602 =
              let uu____1603 =
                let uu____1606 = aux shift t2 in (uu____1606, r) in
              LblPos uu____1603 in
            mk uu____1602 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1625 =
              let uu____1635 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____1644 = aux shift1 body in
              (qop, uu____1635, wopt, vars, uu____1644) in
            mkQuant uu____1625 t1.rng
        | Let (es,body) ->
            let uu____1653 =
              FStar_List.fold_left
                (fun uu____1660  ->
                   fun e  ->
                     match uu____1660 with
                     | (ix,es1) ->
                         let uu____1672 =
                           let uu____1674 = aux shift e in uu____1674 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____1672))
                (shift, []) es in
            (match uu____1653 with
             | (shift1,es_rev) ->
                 let uu____1681 =
                   let uu____1685 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____1685) in
                 mkLet uu____1681 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____1696 = abstr [fv] t in inst [s] uu____1696
let mkQuant':
  (qop* term Prims.list Prims.list* Prims.int Prims.option* fv Prims.list*
    term) -> FStar_Range.range -> term
  =
  fun uu____1710  ->
    match uu____1710 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1735 =
          let uu____1745 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____1754 = FStar_List.map fv_sort vars in
          let uu____1758 = abstr vars body in
          (qop, uu____1745, wopt, uu____1754, uu____1758) in
        mkQuant uu____1735
let mkForall'':
  (pat Prims.list Prims.list* Prims.int Prims.option* sort Prims.list* term)
    -> FStar_Range.range -> term
  =
  fun uu____1775  ->
    fun r  ->
      match uu____1775 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list* Prims.int Prims.option* fvs* term) ->
    FStar_Range.range -> term
  =
  fun uu____1812  ->
    fun r  ->
      match uu____1812 with
      | (pats,wopt,vars,body) ->
          let uu____1831 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____1831 r
let mkForall:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1846  ->
    fun r  ->
      match uu____1846 with
      | (pats,vars,body) ->
          let uu____1860 = mkQuant' (Forall, pats, None, vars, body) in
          uu____1860 r
let mkExists:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1875  ->
    fun r  ->
      match uu____1875 with
      | (pats,vars,body) ->
          let uu____1889 = mkQuant' (Exists, pats, None, vars, body) in
          uu____1889 r
let mkLet': ((fv* term) Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1904  ->
    fun r  ->
      match uu____1904 with
      | (bindings,body) ->
          let uu____1919 = FStar_List.split bindings in
          (match uu____1919 with
           | (vars,es) ->
               let uu____1930 =
                 let uu____1934 = abstr vars body in (es, uu____1934) in
               mkLet uu____1930 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string* (Prims.string* sort) Prims.list* sort* term* caption) ->
    decl
  =
  fun uu____1946  ->
    match uu____1946 with
    | (nm,vars,s,tm,c) ->
        let uu____1966 =
          let uu____1973 = FStar_List.map fv_sort vars in
          let uu____1977 = abstr vars tm in
          (nm, uu____1973, s, uu____1977, c) in
        DefineFun uu____1966
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____1982 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____1982
let fresh_token: (Prims.string* sort) -> Prims.int -> decl =
  fun uu____1989  ->
    fun id  ->
      match uu____1989 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let uu____1996 =
            let uu____2000 =
              let uu____2001 =
                let uu____2004 = mkInteger' id norng in
                let uu____2005 =
                  let uu____2006 =
                    let uu____2010 = constr_id_of_sort sort in
                    let uu____2011 =
                      let uu____2013 = mkApp (tok_name, []) norng in
                      [uu____2013] in
                    (uu____2010, uu____2011) in
                  mkApp uu____2006 norng in
                (uu____2004, uu____2005) in
              mkEq uu____2001 norng in
            (uu____2000, (Some "fresh token"), a_name) in
          Assume uu____1996
let fresh_constructor:
  (Prims.string* sort Prims.list* sort* Prims.int) -> decl =
  fun uu____2024  ->
    match uu____2024 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2043 =
                      let uu____2046 =
                        let uu____2047 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2047 in
                      (uu____2046, s) in
                    mkFreeV uu____2043 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2053 =
            let uu____2057 = constr_id_of_sort sort in (uu____2057, [capp]) in
          mkApp uu____2053 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let uu____2060 =
          let uu____2064 =
            let uu____2065 =
              let uu____2071 =
                let uu____2072 =
                  let uu____2075 = mkInteger id1 norng in
                  (uu____2075, cid_app) in
                mkEq uu____2072 norng in
              ([[capp]], bvar_names, uu____2071) in
            mkForall uu____2065 norng in
          (uu____2064, (Some "Constructor distinct"), a_name) in
        Assume uu____2060
let injective_constructor:
  (Prims.string* constructor_field Prims.list* sort) -> decl Prims.list =
  fun uu____2088  ->
    match uu____2088 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2104 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2104 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2121 = let uu____2124 = bvar_name i in (uu____2124, s) in
          mkFreeV uu____2121 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2133  ->
                    match uu____2133 with
                    | (uu____2137,s,uu____2139) ->
                        let uu____2140 = bvar i s in uu____2140 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2147 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2158  ->
                    match uu____2158 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector")) in
                        if projectible
                        then
                          let a_name =
                            Prims.strcat "projection_inverse_" name1 in
                          let uu____2173 =
                            let uu____2175 =
                              let uu____2176 =
                                let uu____2180 =
                                  let uu____2181 =
                                    let uu____2187 =
                                      let uu____2188 =
                                        let uu____2191 =
                                          let uu____2192 = bvar i s in
                                          uu____2192 norng in
                                        (cproj_app, uu____2191) in
                                      mkEq uu____2188 norng in
                                    ([[capp]], bvar_names, uu____2187) in
                                  mkForall uu____2181 norng in
                                (uu____2180, (Some "Projection inverse"),
                                  a_name) in
                              Assume uu____2176 in
                            [uu____2175] in
                          proj_name :: uu____2173
                        else [proj_name])) in
        FStar_All.pipe_right uu____2147 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2207  ->
    match uu____2207 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2223  ->
                  match uu____2223 with
                  | (uu____2227,sort1,uu____2229) -> sort1)) in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2242 =
              let uu____2245 =
                let uu____2246 =
                  let uu____2250 = constr_id_of_sort sort in
                  (uu____2250, [xx]) in
                mkApp uu____2246 norng in
              let uu____2252 =
                let uu____2253 = FStar_Util.string_of_int id in
                mkInteger uu____2253 norng in
              (uu____2245, uu____2252) in
            mkEq uu____2242 norng in
          let uu____2254 =
            let uu____2262 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2285  ->
                        match uu____2285 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2302 = mkApp (proj, [xx]) norng in
                              (uu____2302, [])
                            else
                              (let fi =
                                 let uu____2313 =
                                   let uu____2314 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2314 in
                                 (uu____2313, s) in
                               let uu____2315 = mkFreeV fi norng in
                               (uu____2315, [fi])))) in
            FStar_All.pipe_right uu____2262 FStar_List.split in
          match uu____2254 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2358 =
                  let uu____2361 = mkApp (name, proj_terms) norng in
                  (xx, uu____2361) in
                mkEq uu____2358 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2366 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____2389 =
          let uu____2391 =
            let uu____2392 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2392 in
          uu____2391 :: cdecl :: cid :: projs in
        let uu____2393 =
          let uu____2395 =
            let uu____2397 =
              let uu____2398 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2398 in
            [uu____2397] in
          FStar_List.append [disc] uu____2395 in
        FStar_List.append uu____2389 uu____2393
let name_binders_inner:
  Prims.string Prims.option ->
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
          let uu____2428 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2451  ->
                    fun s  ->
                      match uu____2451 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2479 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1 in
                          let nm =
                            let uu____2483 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2483 in
                          let names1 = (nm, s) :: names in
                          let b =
                            let uu____2491 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2491 in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2428 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string* sort) Prims.list* Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2533 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts in
    match uu____2533 with
    | (names,binders,n1) -> ((FStar_List.rev names), binders)
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
            (let uu____2587 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____2587) in
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
                             "Prims.guard_free",{ tm = BoundV uu____2609;
                                                  freevars = uu____2610;
                                                  rng = uu____2611;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____2619 -> tm)))) in
      let rec aux' depth n1 names t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____2655 = FStar_List.nth names i in
            FStar_All.pipe_right uu____2655 Prims.fst
        | FreeV x -> Prims.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____2665 =
              let uu____2666 = FStar_List.map (aux1 n1 names) tms in
              FStar_All.pipe_right uu____2666 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2665
        | Labeled (t2,uu____2670,uu____2671) -> aux1 n1 names t2
        | LblPos (t2,s) ->
            let uu____2674 = aux1 n1 names t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____2674 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____2689 = name_binders_inner None names n1 sorts in
            (match uu____2689 with
             | (names1,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[]|[] -> ";;no pats"
                   | uu____2717 ->
                       let uu____2720 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____2728 =
                                   let uu____2729 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____2732 = aux1 n2 names1 p in
                                          FStar_Util.format1 "%s" uu____2732)
                                       pats2 in
                                   FStar_String.concat " " uu____2729 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____2728)) in
                       FStar_All.pipe_right uu____2720
                         (FStar_String.concat "\n") in
                 let uu____2734 =
                   let uu____2736 =
                     let uu____2738 =
                       let uu____2740 = aux1 n2 names1 body in
                       let uu____2741 =
                         let uu____2743 = weightToSmt wopt in
                         [uu____2743; pats_str; qid] in
                       uu____2740 :: uu____2741 in
                     binders1 :: uu____2738 in
                   (qop_to_string qop) :: uu____2736 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____2734)
        | Let (es,body) ->
            let uu____2748 =
              FStar_List.fold_left
                (fun uu____2763  ->
                   fun e  ->
                     match uu____2763 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____2791 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____2791 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____2799 = aux1 n1 names e in
                           FStar_Util.format2 "(%s %s)" nm uu____2799 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names, [], n1) es in
            (match uu____2748 with
             | (names1,binders,n2) ->
                 let uu____2817 = aux1 n2 names1 body in
                 FStar_Util.format2 "(let (%s) %s)"
                   (FStar_String.concat " " binders) uu____2817)
      and aux depth n1 names t1 =
        let s = aux' depth n1 names t1 in
        if t1.rng <> norng
        then
          let uu____2824 = FStar_Range.string_of_range t1.rng in
          let uu____2825 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2824
            uu____2825 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string: Prims.string Prims.option -> Prims.string =
  fun uu___90_2830  ->
    match uu___90_2830 with
    | None  -> ""
    | Some c ->
        let uu____2833 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2842 -> (hd1, "...") in
        (match uu____2833 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2859 =
            FStar_All.pipe_right (FStar_Util.splitlines c)
              (fun uu___91_2861  ->
                 match uu___91_2861 with | [] -> "" | h::t -> h) in
          FStar_Util.format1 "\n; %s" uu____2859
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____2874 = caption_to_string c in
          let uu____2875 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2874 f
            (FStar_String.concat " " l) uu____2875
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2883 = name_macro_binders arg_sorts in
          (match uu____2883 with
           | (names,binders) ->
               let body1 =
                 let uu____2901 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names in
                 inst uu____2901 body in
               let uu____2908 = caption_to_string c in
               let uu____2909 = strSort retsort in
               let uu____2910 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2908
                 f (FStar_String.concat " " binders) uu____2909 uu____2910)
      | Assume (t,c,n1) ->
          let n2 = escape n1 in
          let uu____2915 = caption_to_string c in
          let uu____2916 = termToSmt n2 t in
          FStar_Util.format3 "%s(assert (! %s\n:named %s))" uu____2915
            uu____2916 n2
      | Eval t ->
          let uu____2918 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____2918
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
      | PrintStats  -> "(get-info :all-statistics)"
and mkPrelude: Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n" in
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
      let uu____3122 =
        let uu____3124 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3124
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3122 (FStar_String.concat "\n") in
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
      let uu____3149 =
        let uu____3153 = let uu____3155 = mkInteger' i norng in [uu____3155] in
        ("Tm_uvar", uu____3153) in
      mkApp uu____3149 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let boxInt: term -> term = fun t  -> mkApp ("BoxInt", [t]) t.rng
let unboxInt: term -> term = fun t  -> mkApp ("BoxInt_proj_0", [t]) t.rng
let boxBool: term -> term = fun t  -> mkApp ("BoxBool", [t]) t.rng
let unboxBool: term -> term = fun t  -> mkApp ("BoxBool_proj_0", [t]) t.rng
let boxString: term -> term = fun t  -> mkApp ("BoxString", [t]) t.rng
let unboxString: term -> term =
  fun t  -> mkApp ("BoxString_proj_0", [t]) t.rng
let boxRef: term -> term = fun t  -> mkApp ("BoxRef", [t]) t.rng
let unboxRef: term -> term = fun t  -> mkApp ("BoxRef_proj_0", [t]) t.rng
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | uu____3196 -> Prims.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3203 -> Prims.raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3211::t1::t2::[]);
                       freevars = uu____3214; rng = uu____3215;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3222::t1::t2::[]);
                       freevars = uu____3225; rng = uu____3226;_}::[])
        -> let uu____3233 = mkEq (t1, t2) norng in mkNot uu____3233 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3236; rng = uu____3237;_}::[])
        ->
        let uu____3244 =
          let uu____3247 = unboxInt t1 in
          let uu____3248 = unboxInt t2 in (uu____3247, uu____3248) in
        mkLTE uu____3244 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3251; rng = uu____3252;_}::[])
        ->
        let uu____3259 =
          let uu____3262 = unboxInt t1 in
          let uu____3263 = unboxInt t2 in (uu____3262, uu____3263) in
        mkLT uu____3259 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3266; rng = uu____3267;_}::[])
        ->
        let uu____3274 =
          let uu____3277 = unboxInt t1 in
          let uu____3278 = unboxInt t2 in (uu____3277, uu____3278) in
        mkGTE uu____3274 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3281; rng = uu____3282;_}::[])
        ->
        let uu____3289 =
          let uu____3292 = unboxInt t1 in
          let uu____3293 = unboxInt t2 in (uu____3292, uu____3293) in
        mkGT uu____3289 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3296; rng = uu____3297;_}::[])
        ->
        let uu____3304 =
          let uu____3307 = unboxBool t1 in
          let uu____3308 = unboxBool t2 in (uu____3307, uu____3308) in
        mkAnd uu____3304 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3311; rng = uu____3312;_}::[])
        ->
        let uu____3319 =
          let uu____3322 = unboxBool t1 in
          let uu____3323 = unboxBool t2 in (uu____3322, uu____3323) in
        mkOr uu____3319 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3325; rng = uu____3326;_}::[])
        -> let uu____3333 = unboxBool t1 in mkNot uu____3333 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___92_3336 = unboxBool t1 in
        {
          tm = (uu___92_3336.tm);
          freevars = (uu___92_3336.freevars);
          rng = (t.rng)
        }
    | uu____3339 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3368 = FStar_Options.unthrottle_inductives () in
        if uu____3368
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel: term Prims.option -> term -> term -> term =
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
      let uu____3432 =
        let uu____3436 = let uu____3438 = mkInteger' i norng in [uu____3438] in
        ("FString_const", uu____3436) in
      mkApp uu____3432 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3449 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3449 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3466 =
         let uu____3470 =
           let uu____3472 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3472] in
         ("SFuel", uu____3470) in
       mkApp uu____3466 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term Prims.option ->
    term Prims.option -> FStar_Range.range -> term Prims.option
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (Some p11,Some p21) ->
            let uu____3495 = mkAnd (p11, p21) r in Some uu____3495
        | (Some p,None )|(None ,Some p) -> Some p
        | (None ,None ) -> None
let mk_and_opt_l:
  term Prims.option Prims.list -> FStar_Range.range -> term Prims.option =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3528 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3528
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3539 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3539
let mk_haseq: term -> term =
  fun t  ->
    let uu____3545 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____3545
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3559 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____3559
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (Prims.fst fv)
    | App (op,l) ->
        let uu____3567 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3567
    | Labeled (t1,r1,r2) ->
        let uu____3571 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3571
    | LblPos (t1,s) ->
        let uu____3574 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3574
    | Quant (qop,l,uu____3577,uu____3578,t1) ->
        let uu____3588 = print_smt_term_list_list l in
        let uu____3589 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3588
          uu____3589
    | Let (es,body) ->
        let uu____3594 = print_smt_term_list es in
        let uu____3595 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____3594 uu____3595
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____3598 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____3598 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3608 =
             let uu____3609 =
               let uu____3610 = print_smt_term_list l1 in
               Prims.strcat uu____3610 " ] " in
             Prims.strcat "; [ " uu____3609 in
           Prims.strcat s uu____3608) "" l