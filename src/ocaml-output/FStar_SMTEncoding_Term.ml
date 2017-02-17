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
        let _0_171 = strSort s1 in
        let _0_170 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" _0_171 _0_170
    | Arrow (s1,s2) ->
        let _0_173 = strSort s1 in
        let _0_172 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" _0_173 _0_172
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
    match projectee with | TrueOp  -> true | uu____104 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____108 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____112 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____116 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____120 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____124 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____128 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____132 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____136 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____140 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____144 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____148 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____152 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____156 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____160 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____164 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____168 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____172 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____176 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____181 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____192 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____196 -> false
type term' =
  | Integer of Prims.string
  | BoundV of Prims.int
  | FreeV of (Prims.string* sort)
  | App of (op* term Prims.list)
  | Quant of (qop* term Prims.list Prims.list* Prims.int Prims.option* sort
  Prims.list* term)
  | Labeled of (term* Prims.string* FStar_Range.range)
  | LblPos of (term* Prims.string)
and term =
  {
  tm: term';
  freevars: (Prims.string* sort) Prims.list FStar_Syntax_Syntax.memo;
  rng: FStar_Range.range;}
let uu___is_Integer: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____255 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____267 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____281 -> false
let __proj__FreeV__item___0: term' -> (Prims.string* sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____302 -> false
let __proj__App__item___0: term' -> (op* term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____332 -> false
let __proj__Quant__item___0:
  term' ->
    (qop* term Prims.list Prims.list* Prims.int Prims.option* sort
      Prims.list* term)
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____374 -> false
let __proj__Labeled__item___0:
  term' -> (term* Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____397 -> false
let __proj__LblPos__item___0: term' -> (term* Prims.string) =
  fun projectee  -> match projectee with | LblPos _0 -> _0
type pat = term
type fv = (Prims.string* sort)
type fvs = (Prims.string* sort) Prims.list
type caption = Prims.string Prims.option
type binders = (Prims.string* sort) Prims.list
type projector = (Prims.string* sort)
type constructor_t =
  (Prims.string* projector Prims.list* sort* Prims.int* Prims.bool)
type constructors = constructor_t Prims.list
type decl =
  | DefPrelude
  | DeclFun of (Prims.string* sort Prims.list* sort* caption)
  | DefineFun of (Prims.string* sort Prims.list* sort* term* caption)
  | Assume of (term* caption* Prims.string Prims.option)
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
    match projectee with | DefPrelude  -> true | uu____492 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____502 -> false
let __proj__DeclFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____535 -> false
let __proj__DefineFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* term* caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____569 -> false
let __proj__Assume__item___0:
  decl -> (term* caption* Prims.string Prims.option) =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____593 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____605 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____617 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____628 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____632 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____636 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____640 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____647 -> false
let __proj__SetOption__item___0: decl -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_PrintStats: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | PrintStats  -> true | uu____664 -> false
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
      | (FreeV x,FreeV y) -> fv_eq x y
      | uu____701 -> false
let freevar_sort: term -> sort =
  fun uu___83_706  ->
    match uu___83_706 with
    | { tm = FreeV x; freevars = uu____708; rng = uu____709;_} -> fv_sort x
    | uu____716 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___84_719  ->
    match uu___84_719 with
    | { tm = FreeV fv; freevars = uu____721; rng = uu____722;_} -> fv
    | uu____729 -> failwith "impossible"
let rec freevars: term -> (Prims.string* sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____750,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t)|Labeled (t,_,_)|LblPos (t,_) -> freevars t
let free_variables: term -> fvs =
  fun t  ->
    let uu____771 = FStar_ST.read t.freevars in
    match uu____771 with
    | Some b -> b
    | None  ->
        let fvs =
          let _0_174 = freevars t in FStar_Util.remove_dups fv_eq _0_174 in
        (FStar_ST.write t.freevars (Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___85_804  ->
    match uu___85_804 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___86_807  ->
    match uu___86_807 with
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
  fun uu___87_812  ->
    match uu___87_812 with
    | None  -> ""
    | Some i ->
        let _0_175 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" _0_175
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let _0_176 = FStar_Util.string_of_int i in Prims.strcat "@" _0_176
    | FreeV x ->
        let _0_178 =
          let _0_177 = strSort (Prims.snd x) in Prims.strcat ":" _0_177 in
        Prims.strcat (Prims.fst x) _0_178
    | App (op,tms) ->
        let _0_182 =
          let _0_181 =
            let _0_180 =
              let _0_179 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right _0_179 (FStar_String.concat " ") in
            Prims.strcat _0_180 ")" in
          Prims.strcat (op_to_string op) _0_181 in
        Prims.strcat "(" _0_182
    | Labeled (t,r1,r2) ->
        let _0_185 = hash_of_term t in
        let _0_184 =
          let _0_183 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 _0_183 in
        Prims.strcat _0_185 _0_184
    | LblPos (t,r) ->
        let _0_187 =
          let _0_186 = hash_of_term t in
          Prims.strcat _0_186 (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " _0_187
    | Quant (qop,pats,wopt,sorts,body) ->
        let _0_203 =
          let _0_202 =
            let _0_201 =
              let _0_200 =
                let _0_188 = FStar_List.map strSort sorts in
                FStar_All.pipe_right _0_188 (FStar_String.concat " ") in
              let _0_199 =
                let _0_198 =
                  let _0_197 = hash_of_term body in
                  let _0_196 =
                    let _0_195 =
                      let _0_194 = weightToSmt wopt in
                      let _0_193 =
                        let _0_192 =
                          let _0_191 =
                            let _0_190 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats  ->
                                      let _0_189 =
                                        FStar_List.map hash_of_term pats in
                                      FStar_All.pipe_right _0_189
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right _0_190
                              (FStar_String.concat "; ") in
                          Prims.strcat _0_191 "))" in
                        Prims.strcat " " _0_192 in
                      Prims.strcat _0_194 _0_193 in
                    Prims.strcat " " _0_195 in
                  Prims.strcat _0_197 _0_196 in
                Prims.strcat ")(! " _0_198 in
              Prims.strcat _0_200 _0_199 in
            Prims.strcat " (" _0_201 in
          Prims.strcat (qop_to_string qop) _0_202 in
        Prims.strcat "(" _0_203
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let _0_204 = FStar_Util.mk_ref None in
      { tm = t; freevars = _0_204; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let _0_205 = Integer (FStar_Util.ensure_decimal i) in mk _0_205 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  -> let _0_206 = FStar_Util.string_of_int i in mkInteger _0_206 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV: (Prims.string* sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r
let mkApp': (op* term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r
let mkApp: (Prims.string* term Prims.list) -> FStar_Range.range -> term =
  fun uu____928  ->
    fun r  -> match uu____928 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____944) -> mkFalse r
      | App (FalseOp ,uu____947) -> mkTrue r
      | uu____950 -> mkApp' (Not, [t]) r
let mkAnd: (term* term) -> FStar_Range.range -> term =
  fun uu____958  ->
    fun r  ->
      match uu____958 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____964),uu____965) -> t2
           | (uu____968,App (TrueOp ,uu____969)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____985,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____991) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____995 -> mkApp' (And, [t1; t2]) r)
let mkOr: (term* term) -> FStar_Range.range -> term =
  fun uu____1005  ->
    fun r  ->
      match uu____1005 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1017),uu____1018) -> t2
           | (uu____1021,App (FalseOp ,uu____1022)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1032,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1038) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1042 -> mkApp' (Or, [t1; t2]) r)
let mkImp: (term* term) -> FStar_Range.range -> term =
  fun uu____1052  ->
    fun r  ->
      match uu____1052 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1064),uu____1065) -> t2
           | (uu____1068,App (Imp ,t1'::t2'::[])) ->
               let _0_209 =
                 let _0_208 = let _0_207 = mkAnd (t1, t1') r in [_0_207; t2'] in
                 (Imp, _0_208) in
               mkApp' _0_209 r
           | uu____1073 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op: op -> (term* term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1086  ->
      fun r  -> match uu____1086 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
  fun uu____1173  ->
    fun r  ->
      match uu____1173 with
      | (t1,t2,t3) ->
          (match ((t2.tm), (t3.tm)) with
           | (App (TrueOp ,uu____1181),App (TrueOp ,uu____1182)) -> mkTrue r
           | (App (TrueOp ,uu____1187),uu____1188) ->
               let _0_211 = let _0_210 = mkNot t1 t1.rng in (_0_210, t3) in
               mkImp _0_211 r
           | (uu____1191,App (TrueOp ,uu____1192)) -> mkImp (t1, t2) r
           | (uu____1195,uu____1196) -> mkApp' (ITE, [t1; t2; t3]) r)
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd::tl ->
          FStar_List.fold_left (fun out  -> fun t  -> mkAnd (out, t) r) hd tl
let mkQuant:
  (qop* term Prims.list Prims.list* Prims.int Prims.option* sort Prims.list*
    term) -> FStar_Range.range -> term
  =
  fun uu____1224  ->
    fun r  ->
      match uu____1224 with
      | (qop,pats,wopt,vars,body) ->
          (match (FStar_List.length vars) = (Prims.parse_int "0") with
           | true  -> body
           | uu____1250 ->
               (match body.tm with
                | App (TrueOp ,uu____1251) -> body
                | uu____1254 -> mk (Quant (qop, pats, wopt, vars, body)) r))
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1274 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1274 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t =
        let uu____1288 = FStar_ST.read t.freevars in
        match uu____1288 with
        | Some [] -> t
        | uu____1304 ->
            (match t.tm with
             | Integer _|BoundV _ -> t
             | FreeV x ->
                 let uu____1314 = index_of x in
                 (match uu____1314 with
                  | None  -> t
                  | Some i -> mkBoundV (i + ix) t.rng)
             | App (op,tms) ->
                 let _0_213 =
                   let _0_212 = FStar_List.map (aux ix) tms in (op, _0_212) in
                 mkApp' _0_213 t.rng
             | Labeled (t,r1,r2) ->
                 let _0_215 =
                   Labeled (let _0_214 = aux ix t in (_0_214, r1, r2)) in
                 mk _0_215 t.rng
             | LblPos (t,r) ->
                 let _0_217 = LblPos (let _0_216 = aux ix t in (_0_216, r)) in
                 mk _0_217 t.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n = FStar_List.length vars in
                 let _0_220 =
                   let _0_219 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n)))) in
                   let _0_218 = aux (ix + n) body in
                   (qop, _0_219, wopt, vars, _0_218) in
                 mkQuant _0_220 t.rng) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms = FStar_List.rev tms in
      let n = FStar_List.length tms in
      let rec aux shift t =
        match t.tm with
        | Integer _|FreeV _ -> t
        | BoundV i ->
            (match ((Prims.parse_int "0") <= (i - shift)) &&
                     ((i - shift) < n)
             with
             | true  -> FStar_List.nth tms (i - shift)
             | uu____1380 -> t)
        | App (op,tms) ->
            let _0_222 =
              let _0_221 = FStar_List.map (aux shift) tms in (op, _0_221) in
            mkApp' _0_222 t.rng
        | Labeled (t,r1,r2) ->
            let _0_224 =
              Labeled (let _0_223 = aux shift t in (_0_223, r1, r2)) in
            mk _0_224 t.rng
        | LblPos (t,r) ->
            let _0_226 = LblPos (let _0_225 = aux shift t in (_0_225, r)) in
            mk _0_226 t.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift = shift + m in
            let _0_229 =
              let _0_228 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift))) in
              let _0_227 = aux shift body in
              (qop, _0_228, wopt, vars, _0_227) in
            mkQuant _0_229 t.rng in
      aux (Prims.parse_int "0") t
let mkQuant':
  (qop* term Prims.list Prims.list* Prims.int Prims.option* fv Prims.list*
    term) -> FStar_Range.range -> term
  =
  fun uu____1432  ->
    match uu____1432 with
    | (qop,pats,wopt,vars,body) ->
        mkQuant
          (let _0_232 =
             FStar_All.pipe_right pats
               (FStar_List.map (FStar_List.map (abstr vars))) in
           let _0_231 = FStar_List.map fv_sort vars in
           let _0_230 = abstr vars body in
           (qop, _0_232, wopt, _0_231, _0_230))
let mkForall'':
  (pat Prims.list Prims.list* Prims.int Prims.option* sort Prims.list* term)
    -> FStar_Range.range -> term
  =
  fun uu____1481  ->
    fun r  ->
      match uu____1481 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list* Prims.int Prims.option* fvs* term) ->
    FStar_Range.range -> term
  =
  fun uu____1518  ->
    fun r  ->
      match uu____1518 with
      | (pats,wopt,vars,body) ->
          (mkQuant' (Forall, pats, wopt, vars, body)) r
let mkForall:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1549  ->
    fun r  ->
      match uu____1549 with
      | (pats,vars,body) -> (mkQuant' (Forall, pats, None, vars, body)) r
let mkExists:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1575  ->
    fun r  ->
      match uu____1575 with
      | (pats,vars,body) -> (mkQuant' (Exists, pats, None, vars, body)) r
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string* (Prims.string* sort) Prims.list* sort* term* caption) ->
    decl
  =
  fun uu____1602  ->
    match uu____1602 with
    | (nm,vars,s,tm,c) ->
        DefineFun
          (let _0_234 = FStar_List.map fv_sort vars in
           let _0_233 = abstr vars tm in (nm, _0_234, s, _0_233, c))
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let _0_235 = strSort sort in FStar_Util.format1 "%s_constr_id" _0_235
let fresh_token: (Prims.string* sort) -> Prims.int -> decl =
  fun uu____1634  ->
    fun id  ->
      match uu____1634 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          Assume
            (let _0_243 =
               let _0_242 =
                 let _0_241 = mkInteger' id norng in
                 let _0_240 =
                   let _0_239 =
                     let _0_238 = constr_id_of_sort sort in
                     let _0_237 =
                       let _0_236 = mkApp (tok_name, []) norng in [_0_236] in
                     (_0_238, _0_237) in
                   mkApp _0_239 norng in
                 (_0_241, _0_240) in
               mkEq _0_242 norng in
             (_0_243, (Some "fresh token"), (Some a_name)))
let fresh_constructor:
  (Prims.string* sort Prims.list* sort* Prims.int) -> decl =
  fun uu____1652  ->
    match uu____1652 with
    | (name,arg_sorts,sort,id) ->
        let id = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let _0_246 =
                      let _0_245 =
                        let _0_244 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" _0_244 in
                      (_0_245, s) in
                    mkFreeV _0_246 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let _0_248 =
            let _0_247 = constr_id_of_sort sort in (_0_247, [capp]) in
          mkApp _0_248 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        Assume
          (let _0_253 =
             let _0_252 =
               let _0_251 =
                 let _0_250 =
                   let _0_249 = mkInteger id norng in (_0_249, cid_app) in
                 mkEq _0_250 norng in
               ([[capp]], bvar_names, _0_251) in
             mkForall _0_252 norng in
           (_0_253, (Some "Constructor distinct"), (Some a_name)))
let injective_constructor:
  (Prims.string* (Prims.string* sort) Prims.list* sort) -> decl Prims.list =
  fun uu____1693  ->
    match uu____1693 with
    | (name,projectors,sort) ->
        let n_bvars = FStar_List.length projectors in
        let bvar_name i =
          let _0_254 = FStar_Util.string_of_int i in Prims.strcat "x_" _0_254 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s = mkFreeV (let _0_255 = bvar_name i in (_0_255, s)) in
        let bvars =
          FStar_All.pipe_right projectors
            (FStar_List.mapi
               (fun i  ->
                  fun uu____1742  ->
                    match uu____1742 with
                    | (uu____1745,s) -> (bvar i s) norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let _0_263 =
          FStar_All.pipe_right projectors
            (FStar_List.mapi
               (fun i  ->
                  fun uu____1763  ->
                    match uu____1763 with
                    | (name,s) ->
                        let cproj_app = mkApp (name, [capp]) norng in
                        let proj_name =
                          DeclFun (name, [sort], s, (Some "Projector")) in
                        let a_name = Prims.strcat "projection_inverse_" name in
                        let _0_262 =
                          let _0_261 =
                            Assume
                              (let _0_260 =
                                 let _0_259 =
                                   let _0_258 =
                                     let _0_257 =
                                       let _0_256 = (bvar i s) norng in
                                       (cproj_app, _0_256) in
                                     mkEq _0_257 norng in
                                   ([[capp]], bvar_names, _0_258) in
                                 mkForall _0_259 norng in
                               (_0_260, (Some "Projection inverse"),
                                 (Some a_name))) in
                          [_0_261] in
                        proj_name :: _0_262)) in
        FStar_All.pipe_right _0_263 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____1784  ->
    match uu____1784 with
    | (name,projectors,sort,id,injective) ->
        let injective = injective || true in
        let cdecl =
          DeclFun
            (let _0_264 =
               FStar_All.pipe_right projectors (FStar_List.map Prims.snd) in
             (name, _0_264, sort, (Some "Constructor"))) in
        let cid =
          fresh_constructor
            (let _0_265 =
               FStar_All.pipe_right projectors (FStar_List.map Prims.snd) in
             (name, _0_265, sort, id)) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let _0_271 =
              let _0_270 =
                let _0_267 =
                  let _0_266 = constr_id_of_sort sort in (_0_266, [xx]) in
                mkApp _0_267 norng in
              let _0_269 =
                let _0_268 = FStar_Util.string_of_int id in
                mkInteger _0_268 norng in
              (_0_270, _0_269) in
            mkEq _0_271 norng in
          let proj_terms =
            FStar_All.pipe_right projectors
              (FStar_List.map
                 (fun uu____1820  ->
                    match uu____1820 with
                    | (proj,s) -> mkApp (proj, [xx]) norng)) in
          let disc_inv_body =
            let _0_273 =
              let _0_272 = mkApp (name, proj_terms) norng in (xx, _0_272) in
            mkEq _0_273 norng in
          let disc_ax = mkAnd (disc_eq, disc_inv_body) norng in
          mkDefineFun
            (disc_name, [xfv], Bool_sort, disc_ax,
              (Some "Discriminator definition")) in
        let projs =
          match injective with
          | true  -> injective_constructor (name, projectors, sort)
          | uu____1839 -> [] in
        let _0_278 =
          let _0_274 =
            Caption (FStar_Util.format1 "<start constructor %s>" name) in
          _0_274 :: cdecl :: cid :: projs in
        let _0_277 =
          let _0_276 =
            let _0_275 =
              Caption (FStar_Util.format1 "</end constructor %s>" name) in
            [_0_275] in
          FStar_List.append [disc] _0_276 in
        FStar_List.append _0_278 _0_277
let name_binders_inner:
  (Prims.string* sort) Prims.list ->
    Prims.int ->
      sort Prims.list ->
        ((Prims.string* sort) Prims.list* Prims.string Prims.list* Prims.int)
  =
  fun outer_names  ->
    fun start  ->
      fun sorts  ->
        let uu____1864 =
          FStar_All.pipe_right sorts
            (FStar_List.fold_left
               (fun uu____1887  ->
                  fun s  ->
                    match uu____1887 with
                    | (names,binders,n) ->
                        let prefix =
                          match s with
                          | Term_sort  -> "@x"
                          | uu____1915 -> "@u" in
                        let nm =
                          let _0_279 = FStar_Util.string_of_int n in
                          Prims.strcat prefix _0_279 in
                        let names = (nm, s) :: names in
                        let b =
                          let _0_280 = strSort s in
                          FStar_Util.format2 "(%s %s)" nm _0_280 in
                        (names, (b :: binders), (n + (Prims.parse_int "1"))))
               (outer_names, [], start)) in
        match uu____1864 with
        | (names,binders,n) -> (names, (FStar_List.rev binders), n)
let name_binders:
  sort Prims.list ->
    ((Prims.string* sort) Prims.list* Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____1965 = name_binders_inner [] (Prims.parse_int "0") sorts in
    match uu____1965 with
    | (names,binders,n) -> ((FStar_List.rev names), binders)
let termToSmt: term -> Prims.string =
  fun t  ->
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
                           "Prims.guard_free",{ tm = BoundV uu____2022;
                                                freevars = uu____2023;
                                                rng = uu____2024;_}::[])
                          -> tm
                      | App (Var "Prims.guard_free",p::[]) -> p
                      | uu____2032 -> tm)))) in
    let rec aux' n names t =
      match t.tm with
      | Integer i -> i
      | BoundV i ->
          let _0_281 = FStar_List.nth names i in
          FStar_All.pipe_right _0_281 Prims.fst
      | FreeV x -> Prims.fst x
      | App (op,[]) -> op_to_string op
      | App (op,tms) ->
          let _0_283 =
            let _0_282 = FStar_List.map (aux n names) tms in
            FStar_All.pipe_right _0_282 (FStar_String.concat "\n") in
          FStar_Util.format2 "(%s %s)" (op_to_string op) _0_283
      | Labeled (t,uu____2066,uu____2067) -> aux n names t
      | LblPos (t,s) ->
          let _0_284 = aux n names t in
          FStar_Util.format2 "(! %s :lblpos %s)" _0_284 s
      | Quant (qop,pats,wopt,sorts,body) ->
          let uu____2083 = name_binders_inner names n sorts in
          (match uu____2083 with
           | (names,binders,n) ->
               let binders =
                 FStar_All.pipe_right binders (FStar_String.concat " ") in
               let pats = remove_guard_free pats in
               let pats_str =
                 match pats with
                 | []::[]|[] -> ""
                 | uu____2111 ->
                     let _0_288 =
                       FStar_All.pipe_right pats
                         (FStar_List.map
                            (fun pats  ->
                               let _0_287 =
                                 let _0_286 =
                                   FStar_List.map
                                     (fun p  ->
                                        let _0_285 = aux n names p in
                                        FStar_Util.format1 "%s" _0_285) pats in
                                 FStar_String.concat " " _0_286 in
                               FStar_Util.format1 "\n:pattern (%s)" _0_287)) in
                     FStar_All.pipe_right _0_288 (FStar_String.concat "\n") in
               (match (pats, wopt) with
                | ([]::[],None )|([],None ) ->
                    let _0_289 = aux n names body in
                    FStar_Util.format3 "(%s (%s)\n %s);;no pats\n"
                      (qop_to_string qop) binders _0_289
                | uu____2134 ->
                    let _0_291 = aux n names body in
                    let _0_290 = weightToSmt wopt in
                    FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))"
                      (qop_to_string qop) binders _0_291 _0_290 pats_str))
    and aux n names t =
      let s = aux' n names t in
      match t.rng <> norng with
      | true  ->
          let _0_293 = FStar_Range.string_of_range t.rng in
          let _0_292 = FStar_Range.string_of_use_range t.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _0_293 _0_292 s
      | uu____2145 -> s in
    aux (Prims.parse_int "0") [] t
let caption_to_string: Prims.string Prims.option -> Prims.string =
  fun uu___88_2149  ->
    match uu___88_2149 with
    | None  -> ""
    | Some c ->
        let uu____2152 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd::[] -> (hd, "")
          | hd::uu____2161 -> (hd, "...") in
        (match uu____2152 with
         | (hd,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let _0_294 =
            FStar_All.pipe_right (FStar_Util.splitlines c)
              (fun uu___89_2179  ->
                 match uu___89_2179 with | [] -> "" | h::t -> h) in
          FStar_Util.format1 "\n; %s" _0_294
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let _0_296 = caption_to_string c in
          let _0_295 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _0_296 f
            (FStar_String.concat " " l) _0_295
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2199 = name_binders arg_sorts in
          (match uu____2199 with
           | (names,binders) ->
               let body =
                 let _0_297 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names in
                 inst _0_297 body in
               let _0_300 = caption_to_string c in
               let _0_299 = strSort retsort in
               let _0_298 = termToSmt body in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _0_300 f
                 (FStar_String.concat " " binders) _0_299 _0_298)
      | Assume (t,c,Some n) ->
          let _0_302 = caption_to_string c in
          let _0_301 = termToSmt t in
          FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _0_302 _0_301
            (escape n)
      | Assume (t,c,None ) ->
          let _0_304 = caption_to_string c in
          let _0_303 = termToSmt t in
          FStar_Util.format2 "%s(assert %s)" _0_304 _0_303
      | Eval t ->
          let _0_305 = termToSmt t in FStar_Util.format1 "(eval %s)" _0_305
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v) -> FStar_Util.format2 "(set-option :%s %s)" s v
      | PrintStats  -> "(get-info :all-statistics)"
and mkPrelude: Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n" in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort)], String_sort,
         (Prims.parse_int "0"), true);
      ("Tm_type", [], Term_sort, (Prims.parse_int "2"), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort)], Term_sort,
        (Prims.parse_int "3"), false);
      ("Tm_uvar", [("Tm_uvar_fst", Int_sort)], Term_sort,
        (Prims.parse_int "5"), true);
      ("Tm_unit", [], Term_sort, (Prims.parse_int "6"), true);
      ("BoxInt", [("BoxInt_proj_0", Int_sort)], Term_sort,
        (Prims.parse_int "7"), true);
      ("BoxBool", [("BoxBool_proj_0", Bool_sort)], Term_sort,
        (Prims.parse_int "8"), true);
      ("BoxString", [("BoxString_proj_0", String_sort)], Term_sort,
        (Prims.parse_int "9"), true);
      ("BoxRef", [("BoxRef_proj_0", Ref_sort)], Term_sort,
        (Prims.parse_int "10"), true);
      ("LexCons", [("LexCons_0", Term_sort); ("LexCons_1", Term_sort)],
        Term_sort, (Prims.parse_int "11"), true)] in
    let bcons =
      let _0_307 =
        let _0_306 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right _0_306 (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right _0_307 (FStar_String.concat "\n") in
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
      let _0_310 =
        let _0_309 = let _0_308 = mkInteger' i norng in [_0_308] in
        ("Tm_uvar", _0_309) in
      mkApp _0_310 r
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
      | uu____2456 -> Prims.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____2463 -> Prims.raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____2471::t1::t2::[]);
                       freevars = uu____2474; rng = uu____2475;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____2482::t1::t2::[]);
                       freevars = uu____2485; rng = uu____2486;_}::[])
        -> let _0_311 = mkEq (t1, t2) norng in mkNot _0_311 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____2495; rng = uu____2496;_}::[])
        ->
        let _0_314 =
          let _0_313 = unboxInt t1 in
          let _0_312 = unboxInt t2 in (_0_313, _0_312) in
        mkLTE _0_314 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____2505; rng = uu____2506;_}::[])
        ->
        let _0_317 =
          let _0_316 = unboxInt t1 in
          let _0_315 = unboxInt t2 in (_0_316, _0_315) in
        mkLT _0_317 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____2515; rng = uu____2516;_}::[])
        ->
        let _0_320 =
          let _0_319 = unboxInt t1 in
          let _0_318 = unboxInt t2 in (_0_319, _0_318) in
        mkGTE _0_320 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____2525; rng = uu____2526;_}::[])
        ->
        let _0_323 =
          let _0_322 = unboxInt t1 in
          let _0_321 = unboxInt t2 in (_0_322, _0_321) in
        mkGT _0_323 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____2535; rng = uu____2536;_}::[])
        ->
        let _0_326 =
          let _0_325 = unboxBool t1 in
          let _0_324 = unboxBool t2 in (_0_325, _0_324) in
        mkAnd _0_326 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____2545; rng = uu____2546;_}::[])
        ->
        let _0_329 =
          let _0_328 = unboxBool t1 in
          let _0_327 = unboxBool t2 in (_0_328, _0_327) in
        mkOr _0_329 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t::[]);
                       freevars = uu____2554; rng = uu____2555;_}::[])
        -> let _0_330 = unboxBool t in mkNot _0_330 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___90_2564 = unboxBool t1 in
        {
          tm = (uu___90_2564.tm);
          freevars = (uu___90_2564.freevars);
          rng = (t.rng)
        }
    | uu____2567 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v  -> fun t  -> mkApp ("HasType", [v; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v  -> fun t  -> mkApp ("HasTypeZ", [v; t]) t.rng
let mk_IsTyped: term -> term = fun v  -> mkApp ("IsTyped", [v]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v  ->
      fun t  ->
        let uu____2596 = FStar_Options.unthrottle_inductives () in
        match uu____2596 with
        | true  -> mk_HasType v t
        | uu____2597 -> mkApp ("HasTypeFuel", [f; v; t]) t.rng
let mk_HasTypeWithFuel: term Prims.option -> term -> term -> term =
  fun f  ->
    fun v  ->
      fun t  ->
        match f with
        | None  -> mk_HasType v t
        | Some f -> mk_HasTypeFuel f v t
let mk_Destruct: term -> FStar_Range.range -> term =
  fun v  -> mkApp ("Destruct", [v])
let mk_Rank: term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x])
let mk_tester: Prims.string -> term -> term =
  fun n  -> fun t  -> mkApp ((Prims.strcat "is-" n), [t]) t.rng
let mk_ApplyTF: term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng
let mk_ApplyTT: term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r
let mk_String_const: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let _0_333 =
        let _0_332 = let _0_331 = mkInteger' i norng in [_0_331] in
        ("FString_const", _0_332) in
      mkApp _0_333 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let _0_334 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right _0_334 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n  ->
    match n = (Prims.parse_int "0") with
    | true  -> mkApp ("ZFuel", []) norng
    | uu____2678 ->
        let _0_337 =
          let _0_336 =
            let _0_335 = n_fuel (n - (Prims.parse_int "1")) in [_0_335] in
          ("SFuel", _0_336) in
        mkApp _0_337 norng
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
        | (Some p1,Some p2) -> Some (mkAnd (p1, p2) r)
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
      let _0_338 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l _0_338
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let _0_339 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l _0_339
let mk_haseq: term -> term =
  fun t  -> mk_Valid (mkApp ("Prims.hasEq", [t]) t.rng)
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n -> FStar_Util.format1 "(Integer %s)" n
    | BoundV n ->
        let _0_340 = FStar_Util.string_of_int n in
        FStar_Util.format1 "(BoundV %s)" _0_340
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (Prims.fst fv)
    | App (op,l) ->
        let _0_341 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) _0_341
    | Labeled (t,r1,r2) ->
        let _0_342 = print_smt_term t in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 _0_342
    | LblPos (t,s) ->
        let _0_343 = print_smt_term t in
        FStar_Util.format2 "(LblPos %s %s)" s _0_343
    | Quant (qop,l,uu____2775,uu____2776,t) ->
        let _0_345 = print_smt_term_list_list l in
        let _0_344 = print_smt_term t in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _0_345 _0_344
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let _0_346 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right _0_346 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l  ->
           let _0_349 =
             let _0_348 =
               let _0_347 = print_smt_term_list l in
               Prims.strcat _0_347 " ] " in
             Prims.strcat "; [ " _0_348 in
           Prims.strcat s _0_349) "" l