open Prims
type sort =
  | Bool_sort 
  | Int_sort 
  | String_sort 
  | Ref_sort 
  | Term_sort 
  | Fuel_sort 
  | Array of (sort * sort) 
  | Arrow of (sort * sort) 
  | Sort of Prims.string 
let uu___is_Bool_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____17 -> false
  
let uu___is_Int_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____21 -> false
  
let uu___is_String_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____25 -> false
  
let uu___is_Ref_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____29 -> false
  
let uu___is_Term_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____33 -> false
  
let uu___is_Fuel_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____37 -> false
  
let uu___is_Array : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____44 -> false
  
let __proj__Array__item___0 : sort -> (sort * sort) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let uu___is_Arrow : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____64 -> false
  
let __proj__Arrow__item___0 : sort -> (sort * sort) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let uu___is_Sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____82 -> false
  
let __proj__Sort__item___0 : sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0 
let rec strSort : sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Ref_sort  -> "Ref"
    | Fuel_sort  -> "Fuel"
    | Array (s1,s2) ->
        let _0_177 = strSort s1  in
        let _0_176 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" _0_177 _0_176
    | Arrow (s1,s2) ->
        let _0_179 = strSort s1  in
        let _0_178 = strSort s2  in
        FStar_Util.format2 "(%s -> %s)" _0_179 _0_178
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
let uu___is_TrueOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____104 -> false
  
let uu___is_FalseOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____108 -> false
  
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____112 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____116 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____120 -> false 
let uu___is_Imp : op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____124 -> false 
let uu___is_Iff : op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____128 -> false 
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____132 -> false 
let uu___is_LT : op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____136 -> false 
let uu___is_LTE : op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____140 -> false 
let uu___is_GT : op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____144 -> false 
let uu___is_GTE : op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____148 -> false 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____152 -> false 
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____156 -> false 
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____160 -> false 
let uu___is_Mul : op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____164 -> false 
let uu___is_Minus : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____168 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____172 -> false 
let uu___is_ITE : op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____176 -> false 
let uu___is_Var : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____181 -> false
  
let __proj__Var__item___0 : op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let uu___is_Forall : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____192 -> false
  
let uu___is_Exists : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____196 -> false
  
type term' =
  | Integer of Prims.string 
  | BoundV of Prims.int 
  | FreeV of (Prims.string * sort) 
  | App of (op * term Prims.list) 
  | Quant of (qop * term Prims.list Prims.list * Prims.int Prims.option *
  sort Prims.list * term) 
  | Let of (term Prims.list * term) 
  | Labeled of (term * Prims.string * FStar_Range.range) 
  | LblPos of (term * Prims.string) 
and term =
  {
  tm: term' ;
  freevars: (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo ;
  rng: FStar_Range.range }
let uu___is_Integer : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____261 -> false
  
let __proj__Integer__item___0 : term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let uu___is_BoundV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____273 -> false
  
let __proj__BoundV__item___0 : term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let uu___is_FreeV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____287 -> false
  
let __proj__FreeV__item___0 : term' -> (Prims.string * sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____308 -> false
  
let __proj__App__item___0 : term' -> (op * term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Quant : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____338 -> false
  
let __proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int Prims.option * sort
      Prims.list * term)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____380 -> false
  
let __proj__Let__item___0 : term' -> (term Prims.list * term) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____404 -> false
  
let __proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_LblPos : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____427 -> false
  
let __proj__LblPos__item___0 : term' -> (term * Prims.string) =
  fun projectee  -> match projectee with | LblPos _0 -> _0 
type pat = term
type fv = (Prims.string * sort)
type fvs = (Prims.string * sort) Prims.list
type caption = Prims.string Prims.option
type binders = (Prims.string * sort) Prims.list
type constructor_field = (Prims.string * sort * Prims.bool)
type constructor_t =
  (Prims.string * constructor_field Prims.list * sort * Prims.int *
    Prims.bool)
type constructors = constructor_t Prims.list
type decl =
  | DefPrelude 
  | DeclFun of (Prims.string * sort Prims.list * sort * caption) 
  | DefineFun of (Prims.string * sort Prims.list * sort * term * caption) 
  | Assume of (term * caption * Prims.string Prims.option) 
  | Caption of Prims.string 
  | Eval of term 
  | Echo of Prims.string 
  | Push 
  | Pop 
  | CheckSat 
  | GetUnsatCore 
  | SetOption of (Prims.string * Prims.string) 
  | PrintStats 
let uu___is_DefPrelude : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____523 -> false
  
let uu___is_DeclFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____533 -> false
  
let __proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let uu___is_DefineFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____566 -> false
  
let __proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let uu___is_Assume : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____600 -> false
  
let __proj__Assume__item___0 :
  decl -> (term * caption * Prims.string Prims.option) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_Caption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____624 -> false
  
let __proj__Caption__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let uu___is_Eval : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____636 -> false
  
let __proj__Eval__item___0 : decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let uu___is_Echo : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____648 -> false
  
let __proj__Echo__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let uu___is_Push : decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____659 -> false 
let uu___is_Pop : decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____663 -> false 
let uu___is_CheckSat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____667 -> false
  
let uu___is_GetUnsatCore : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____671 -> false
  
let uu___is_SetOption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____678 -> false
  
let __proj__SetOption__item___0 : decl -> (Prims.string * Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let uu___is_PrintStats : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | PrintStats  -> true | uu____695 -> false
  
type decls_t = decl Prims.list
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let fv_eq : fv -> fv -> Prims.bool =
  fun x  -> fun y  -> (Prims.fst x) = (Prims.fst y) 
let fv_sort x = Prims.snd x 
let freevar_eq : term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x,FreeV y) -> fv_eq x y
      | uu____732 -> false
  
let freevar_sort : term -> sort =
  fun uu___82_737  ->
    match uu___82_737 with
    | { tm = FreeV x; freevars = uu____739; rng = uu____740;_} -> fv_sort x
    | uu____747 -> failwith "impossible"
  
let fv_of_term : term -> fv =
  fun uu___83_750  ->
    match uu___83_750 with
    | { tm = FreeV fv; freevars = uu____752; rng = uu____753;_} -> fv
    | uu____760 -> failwith "impossible"
  
let rec freevars : term -> (Prims.string * sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____781,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t)|Labeled (t,_,_)|LblPos (t,_) -> freevars t
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let free_variables : term -> fvs =
  fun t  ->
    let uu____808 = FStar_ST.read t.freevars  in
    match uu____808 with
    | Some b -> b
    | None  ->
        let fvs =
          let _0_180 = freevars t  in FStar_Util.remove_dups fv_eq _0_180  in
        (FStar_ST.write t.freevars (Some fvs); fvs)
  
let qop_to_string : qop -> Prims.string =
  fun uu___84_841  ->
    match uu___84_841 with | Forall  -> "forall" | Exists  -> "exists"
  
let op_to_string : op -> Prims.string =
  fun uu___85_844  ->
    match uu___85_844 with
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
  
let weightToSmt : Prims.int Prims.option -> Prims.string =
  fun uu___86_849  ->
    match uu___86_849 with
    | None  -> ""
    | Some i ->
        let _0_181 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" _0_181
  
let rec hash_of_term' : term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let _0_182 = FStar_Util.string_of_int i  in Prims.strcat "@" _0_182
    | FreeV x ->
        let _0_184 =
          let _0_183 = strSort (Prims.snd x)  in Prims.strcat ":" _0_183  in
        Prims.strcat (Prims.fst x) _0_184
    | App (op,tms) ->
        let _0_188 =
          let _0_187 =
            let _0_186 =
              let _0_185 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right _0_185 (FStar_String.concat " ")  in
            Prims.strcat _0_186 ")"  in
          Prims.strcat (op_to_string op) _0_187  in
        Prims.strcat "(" _0_188
    | Labeled (t,r1,r2) ->
        let _0_191 = hash_of_term t  in
        let _0_190 =
          let _0_189 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 _0_189  in
        Prims.strcat _0_191 _0_190
    | LblPos (t,r) ->
        let _0_193 =
          let _0_192 = hash_of_term t  in
          Prims.strcat _0_192 (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " _0_193
    | Quant (qop,pats,wopt,sorts,body) ->
        let _0_209 =
          let _0_208 =
            let _0_207 =
              let _0_206 =
                let _0_194 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right _0_194 (FStar_String.concat " ")  in
              let _0_205 =
                let _0_204 =
                  let _0_203 = hash_of_term body  in
                  let _0_202 =
                    let _0_201 =
                      let _0_200 = weightToSmt wopt  in
                      let _0_199 =
                        let _0_198 =
                          let _0_197 =
                            let _0_196 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats  ->
                                      let _0_195 =
                                        FStar_List.map hash_of_term pats  in
                                      FStar_All.pipe_right _0_195
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right _0_196
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat _0_197 "))"  in
                        Prims.strcat " " _0_198  in
                      Prims.strcat _0_200 _0_199  in
                    Prims.strcat " " _0_201  in
                  Prims.strcat _0_203 _0_202  in
                Prims.strcat ")(! " _0_204  in
              Prims.strcat _0_206 _0_205  in
            Prims.strcat " (" _0_207  in
          Prims.strcat (qop_to_string qop) _0_208  in
        Prims.strcat "(" _0_209
    | Let (es,body) ->
        let _0_215 =
          let _0_214 =
            let _0_210 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right _0_210 (FStar_String.concat " ")  in
          let _0_213 =
            let _0_212 =
              let _0_211 = hash_of_term body  in Prims.strcat _0_211 ")"  in
            Prims.strcat ") " _0_212  in
          Prims.strcat _0_214 _0_213  in
        Prims.strcat "(let (" _0_215

and hash_of_term : term -> Prims.string = fun tm  -> hash_of_term' tm.tm

let mk : term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let _0_216 = FStar_Util.mk_ref None  in
      { tm = t; freevars = _0_216; rng = r }
  
let mkTrue : FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r 
let mkFalse : FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r 
let mkInteger : Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let _0_217 = Integer (FStar_Util.ensure_decimal i)  in mk _0_217 r
  
let mkInteger' : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  -> let _0_218 = FStar_Util.string_of_int i  in mkInteger _0_218 r
  
let mkBoundV : Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r 
let mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r 
let mkApp' : (op * term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r 
let mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term =
  fun uu____970  ->
    fun r  -> match uu____970 with | (s,args) -> mk (App ((Var s), args)) r
  
let mkNot : term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____986) -> mkFalse r
      | App (FalseOp ,uu____989) -> mkTrue r
      | uu____992 -> mkApp' (Not, [t]) r
  
let mkAnd : (term * term) -> FStar_Range.range -> term =
  fun uu____1000  ->
    fun r  ->
      match uu____1000 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1006),uu____1007) -> t2
           | (uu____1010,App (TrueOp ,uu____1011)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1027,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1033) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1037 -> mkApp' (And, [t1; t2]) r)
  
let mkOr : (term * term) -> FStar_Range.range -> term =
  fun uu____1047  ->
    fun r  ->
      match uu____1047 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1059),uu____1060) -> t2
           | (uu____1063,App (FalseOp ,uu____1064)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1074,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1080) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1084 -> mkApp' (Or, [t1; t2]) r)
  
let mkImp : (term * term) -> FStar_Range.range -> term =
  fun uu____1094  ->
    fun r  ->
      match uu____1094 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1106),uu____1107) -> t2
           | (uu____1110,App (Imp ,t1'::t2'::[])) ->
               let _0_221 =
                 let _0_220 =
                   let _0_219 = mkAnd (t1, t1') r  in [_0_219; t2']  in
                 (Imp, _0_220)  in
               mkApp' _0_221 r
           | uu____1115 -> mkApp' (Imp, [t1; t2]) r)
  
let mk_bin_op : op -> (term * term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1128  ->
      fun r  -> match uu____1128 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
let mkMinus : term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r 
let mkIff : (term * term) -> FStar_Range.range -> term = mk_bin_op Iff 
let mkEq : (term * term) -> FStar_Range.range -> term = mk_bin_op Eq 
let mkLT : (term * term) -> FStar_Range.range -> term = mk_bin_op LT 
let mkLTE : (term * term) -> FStar_Range.range -> term = mk_bin_op LTE 
let mkGT : (term * term) -> FStar_Range.range -> term = mk_bin_op GT 
let mkGTE : (term * term) -> FStar_Range.range -> term = mk_bin_op GTE 
let mkAdd : (term * term) -> FStar_Range.range -> term = mk_bin_op Add 
let mkSub : (term * term) -> FStar_Range.range -> term = mk_bin_op Sub 
let mkDiv : (term * term) -> FStar_Range.range -> term = mk_bin_op Div 
let mkMul : (term * term) -> FStar_Range.range -> term = mk_bin_op Mul 
let mkMod : (term * term) -> FStar_Range.range -> term = mk_bin_op Mod 
let mkITE : (term * term * term) -> FStar_Range.range -> term =
  fun uu____1215  ->
    fun r  ->
      match uu____1215 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1223) -> t2
           | App (FalseOp ,uu____1226) -> t3
           | uu____1229 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1230),App (TrueOp ,uu____1231)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1236),uu____1237) ->
                    let _0_223 =
                      let _0_222 = mkNot t1 t1.rng  in (_0_222, t3)  in
                    mkImp _0_223 r
                | (uu____1240,App (TrueOp ,uu____1241)) -> mkImp (t1, t2) r
                | (uu____1244,uu____1245) -> mkApp' (ITE, [t1; t2; t3]) r))
  
let mkCases : term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd::tl ->
          FStar_List.fold_left (fun out  -> fun t  -> mkAnd (out, t) r) hd tl
  
let mkQuant :
  (qop * term Prims.list Prims.list * Prims.int Prims.option * sort
    Prims.list * term) -> FStar_Range.range -> term
  =
  fun uu____1273  ->
    fun r  ->
      match uu____1273 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1300) -> body
             | uu____1303 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let mkLet : (term Prims.list * term) -> FStar_Range.range -> term =
  fun uu____1315  ->
    fun r  ->
      match uu____1315 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let abstr : fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____1343 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____1343 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1")))  in
      let rec aux ix t =
        let uu____1357 = FStar_ST.read t.freevars  in
        match uu____1357 with
        | Some [] -> t
        | uu____1373 ->
            (match t.tm with
             | Integer _|BoundV _ -> t
             | FreeV x ->
                 let uu____1383 = index_of x  in
                 (match uu____1383 with
                  | None  -> t
                  | Some i -> mkBoundV (i + ix) t.rng)
             | App (op,tms) ->
                 let _0_225 =
                   let _0_224 = FStar_List.map (aux ix) tms  in (op, _0_224)
                    in
                 mkApp' _0_225 t.rng
             | Labeled (t,r1,r2) ->
                 let _0_227 =
                   Labeled (let _0_226 = aux ix t  in (_0_226, r1, r2))  in
                 mk _0_227 t.rng
             | LblPos (t,r) ->
                 let _0_229 = LblPos (let _0_228 = aux ix t  in (_0_228, r))
                    in
                 mk _0_229 t.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n = FStar_List.length vars  in
                 let _0_232 =
                   let _0_231 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n))))
                      in
                   let _0_230 = aux (ix + n) body  in
                   (qop, _0_231, wopt, vars, _0_230)  in
                 mkQuant _0_232 t.rng
             | Let (es,body) ->
                 let uu____1429 =
                   FStar_List.fold_left
                     (fun uu____1436  ->
                        fun e  ->
                          match uu____1436 with
                          | (ix,l) ->
                              let _0_234 =
                                let _0_233 = aux ix e  in _0_233 :: l  in
                              ((ix + (Prims.parse_int "1")), _0_234))
                     (ix, []) es
                    in
                 (match uu____1429 with
                  | (ix,es_rev) ->
                      let _0_236 =
                        let _0_235 = aux ix body  in
                        ((FStar_List.rev es_rev), _0_235)  in
                      mkLet _0_236 t.rng))
         in
      aux (Prims.parse_int "0") t
  
let inst : term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms = FStar_List.rev tms  in
      let n = FStar_List.length tms  in
      let rec aux shift t =
        match t.tm with
        | Integer _|FreeV _ -> t
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n)
            then FStar_List.nth tms (i - shift)
            else t
        | App (op,tms) ->
            let _0_238 =
              let _0_237 = FStar_List.map (aux shift) tms  in (op, _0_237)
               in
            mkApp' _0_238 t.rng
        | Labeled (t,r1,r2) ->
            let _0_240 =
              Labeled (let _0_239 = aux shift t  in (_0_239, r1, r2))  in
            mk _0_240 t.rng
        | LblPos (t,r) ->
            let _0_242 = LblPos (let _0_241 = aux shift t  in (_0_241, r))
               in
            mk _0_242 t.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift = shift + m  in
            let _0_245 =
              let _0_244 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift)))
                 in
              let _0_243 = aux shift body  in
              (qop, _0_244, wopt, vars, _0_243)  in
            mkQuant _0_245 t.rng
        | Let (es,body) ->
            let uu____1522 =
              FStar_List.fold_left
                (fun uu____1529  ->
                   fun e  ->
                     match uu____1529 with
                     | (ix,es) ->
                         let _0_247 =
                           let _0_246 = aux shift e  in _0_246 :: es  in
                         ((shift + (Prims.parse_int "1")), _0_247))
                (shift, []) es
               in
            (match uu____1522 with
             | (shift,es_rev) ->
                 let _0_249 =
                   let _0_248 = aux shift body  in
                   ((FStar_List.rev es_rev), _0_248)  in
                 mkLet _0_249 t.rng)
         in
      aux (Prims.parse_int "0") t
  
let subst : term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let _0_250 = abstr [fv] t  in inst [s] _0_250
  
let mkQuant' :
  (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list
    * term) -> FStar_Range.range -> term
  =
  fun uu____1570  ->
    match uu____1570 with
    | (qop,pats,wopt,vars,body) ->
        mkQuant
          (let _0_253 =
             FStar_All.pipe_right pats
               (FStar_List.map (FStar_List.map (abstr vars)))
              in
           let _0_252 = FStar_List.map fv_sort vars  in
           let _0_251 = abstr vars body  in
           (qop, _0_253, wopt, _0_252, _0_251))
  
let mkForall'' :
  (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list *
    term) -> FStar_Range.range -> term
  =
  fun uu____1619  ->
    fun r  ->
      match uu____1619 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let mkForall' :
  (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term) ->
    FStar_Range.range -> term
  =
  fun uu____1656  ->
    fun r  ->
      match uu____1656 with
      | (pats,wopt,vars,body) ->
          (mkQuant' (Forall, pats, wopt, vars, body)) r
  
let mkForall :
  (pat Prims.list Prims.list * fvs * term) -> FStar_Range.range -> term =
  fun uu____1687  ->
    fun r  ->
      match uu____1687 with
      | (pats,vars,body) -> (mkQuant' (Forall, pats, None, vars, body)) r
  
let mkExists :
  (pat Prims.list Prims.list * fvs * term) -> FStar_Range.range -> term =
  fun uu____1713  ->
    fun r  ->
      match uu____1713 with
      | (pats,vars,body) -> (mkQuant' (Exists, pats, None, vars, body)) r
  
let mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term =
  fun uu____1739  ->
    fun r  ->
      match uu____1739 with
      | (bindings,body) ->
          let uu____1754 = FStar_List.split bindings  in
          (match uu____1754 with
           | (vars,es) ->
               let _0_255 = let _0_254 = abstr vars body  in (es, _0_254)  in
               mkLet _0_255 r)
  
let norng : FStar_Range.range = FStar_Range.dummyRange 
let mkDefineFun :
  (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)
    -> decl
  =
  fun uu____1776  ->
    match uu____1776 with
    | (nm,vars,s,tm,c) ->
        DefineFun
          (let _0_257 = FStar_List.map fv_sort vars  in
           let _0_256 = abstr vars tm  in (nm, _0_257, s, _0_256, c))
  
let constr_id_of_sort : sort -> Prims.string =
  fun sort  ->
    let _0_258 = strSort sort  in FStar_Util.format1 "%s_constr_id" _0_258
  
let fresh_token : (Prims.string * sort) -> Prims.int -> decl =
  fun uu____1808  ->
    fun id  ->
      match uu____1808 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          Assume
            (let _0_266 =
               let _0_265 =
                 let _0_264 = mkInteger' id norng  in
                 let _0_263 =
                   let _0_262 =
                     let _0_261 = constr_id_of_sort sort  in
                     let _0_260 =
                       let _0_259 = mkApp (tok_name, []) norng  in [_0_259]
                        in
                     (_0_261, _0_260)  in
                   mkApp _0_262 norng  in
                 (_0_264, _0_263)  in
               mkEq _0_265 norng  in
             (_0_266, (Some "fresh token"), (Some a_name)))
  
let fresh_constructor :
  (Prims.string * sort Prims.list * sort * Prims.int) -> decl =
  fun uu____1826  ->
    match uu____1826 with
    | (name,arg_sorts,sort,id) ->
        let id = FStar_Util.string_of_int id  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let _0_269 =
                      let _0_268 =
                        let _0_267 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" _0_267  in
                      (_0_268, s)  in
                    mkFreeV _0_269 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let _0_271 =
            let _0_270 = constr_id_of_sort sort  in (_0_270, [capp])  in
          mkApp _0_271 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        Assume
          (let _0_276 =
             let _0_275 =
               let _0_274 =
                 let _0_273 =
                   let _0_272 = mkInteger id norng  in (_0_272, cid_app)  in
                 mkEq _0_273 norng  in
               ([[capp]], bvar_names, _0_274)  in
             mkForall _0_275 norng  in
           (_0_276, (Some "Constructor distinct"), (Some a_name)))
  
let injective_constructor :
  (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list =
  fun uu____1865  ->
    match uu____1865 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let _0_277 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" _0_277  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s = mkFreeV (let _0_278 = bvar_name i  in (_0_278, s))  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____1905  ->
                    match uu____1905 with
                    | (uu____1909,s,uu____1911) -> (bvar i s) norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let _0_286 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____1927  ->
                    match uu____1927 with
                    | (name,s,projectible) ->
                        let cproj_app = mkApp (name, [capp]) norng  in
                        let proj_name =
                          DeclFun (name, [sort], s, (Some "Projector"))  in
                        if projectible
                        then
                          let a_name =
                            Prims.strcat "projection_inverse_" name  in
                          let _0_285 =
                            let _0_284 =
                              Assume
                                (let _0_283 =
                                   let _0_282 =
                                     let _0_281 =
                                       let _0_280 =
                                         let _0_279 = (bvar i s) norng  in
                                         (cproj_app, _0_279)  in
                                       mkEq _0_280 norng  in
                                     ([[capp]], bvar_names, _0_281)  in
                                   mkForall _0_282 norng  in
                                 (_0_283, (Some "Projection inverse"),
                                   (Some a_name)))
                               in
                            [_0_284]  in
                          proj_name :: _0_285
                        else [proj_name]))
           in
        FStar_All.pipe_right _0_286 FStar_List.flatten
  
let constructor_to_decl : constructor_t -> decl Prims.list =
  fun uu____1952  ->
    match uu____1952 with
    | (name,fields,sort,id,injective) ->
        let injective = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____1968  ->
                  match uu____1968 with
                  | (uu____1972,sort,uu____1974) -> sort))
           in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor"))
           in
        let cid = fresh_constructor (name, field_sorts, sort, id)  in
        let disc =
          let disc_name = Prims.strcat "is-" name  in
          let xfv = ("x", sort)  in
          let xx = mkFreeV xfv norng  in
          let disc_eq =
            let _0_292 =
              let _0_291 =
                let _0_288 =
                  let _0_287 = constr_id_of_sort sort  in (_0_287, [xx])  in
                mkApp _0_288 norng  in
              let _0_290 =
                let _0_289 = FStar_Util.string_of_int id  in
                mkInteger _0_289 norng  in
              (_0_291, _0_290)  in
            mkEq _0_292 norng  in
          let uu____1988 =
            let _0_297 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2025  ->
                        match uu____2025 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let _0_293 = mkApp (proj, [xx]) norng  in
                              (_0_293, [])
                            else
                              (let fi =
                                 let _0_295 =
                                   let _0_294 = FStar_Util.string_of_int i
                                      in
                                   Prims.strcat "f_" _0_294  in
                                 (_0_295, s)  in
                               let _0_296 = mkFreeV fi norng  in
                               (_0_296, [fi]))))
               in
            FStar_All.pipe_right _0_297 FStar_List.split  in
          match uu____1988 with
          | (proj_terms,ex_vars) ->
              let ex_vars = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let _0_299 =
                  let _0_298 = mkApp (name, proj_terms) norng  in
                  (xx, _0_298)  in
                mkEq _0_299 norng  in
              let disc_inv_body =
                match ex_vars with
                | [] -> disc_inv_body
                | uu____2085 -> mkExists ([], ex_vars, disc_inv_body) norng
                 in
              let disc_ax = mkAnd (disc_eq, disc_inv_body) norng  in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (Some "Discriminator definition"))
                 in
              def
           in
        let projs =
          if injective
          then injective_constructor (name, fields, sort)
          else []  in
        let _0_304 =
          let _0_300 =
            Caption (FStar_Util.format1 "<start constructor %s>" name)  in
          _0_300 :: cdecl :: cid :: projs  in
        let _0_303 =
          let _0_302 =
            let _0_301 =
              Caption (FStar_Util.format1 "</end constructor %s>" name)  in
            [_0_301]  in
          FStar_List.append [disc] _0_302  in
        FStar_List.append _0_304 _0_303
  
let name_binders_inner :
  Prims.string Prims.option ->
    (Prims.string * sort) Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string * sort) Prims.list * Prims.string Prims.list *
            Prims.int)
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____2137 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2160  ->
                    fun s  ->
                      match uu____2160 with
                      | (names,binders,n) ->
                          let prefix =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2188 -> "@u"  in
                          let prefix =
                            match prefix_opt with
                            | None  -> prefix
                            | Some p -> Prims.strcat p prefix  in
                          let nm =
                            let _0_305 = FStar_Util.string_of_int n  in
                            Prims.strcat prefix _0_305  in
                          let names = (nm, s) :: names  in
                          let b =
                            let _0_306 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm _0_306  in
                          (names, (b :: binders),
                            (n + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____2137 with
          | (names,binders,n) -> (names, (FStar_List.rev binders), n)
  
let name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2240 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts  in
    match uu____2240 with
    | (names,binders,n) -> ((FStar_List.rev names), binders)
  
let termToSmt : term -> Prims.string =
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
                           "Prims.guard_free",{ tm = BoundV uu____2297;
                                                freevars = uu____2298;
                                                rng = uu____2299;_}::[])
                          -> tm
                      | App (Var "Prims.guard_free",p::[]) -> p
                      | uu____2307 -> tm))))
       in
    let rec aux' n names t =
      match t.tm with
      | Integer i -> i
      | BoundV i ->
          let _0_307 = FStar_List.nth names i  in
          FStar_All.pipe_right _0_307 Prims.fst
      | FreeV x -> Prims.fst x
      | App (op,[]) -> op_to_string op
      | App (op,tms) ->
          let _0_309 =
            let _0_308 = FStar_List.map (aux n names) tms  in
            FStar_All.pipe_right _0_308 (FStar_String.concat "\n")  in
          FStar_Util.format2 "(%s %s)" (op_to_string op) _0_309
      | Labeled (t,uu____2341,uu____2342) -> aux n names t
      | LblPos (t,s) ->
          let _0_310 = aux n names t  in
          FStar_Util.format2 "(! %s :lblpos %s)" _0_310 s
      | Quant (qop,pats,wopt,sorts,body) ->
          let uu____2358 = name_binders_inner None names n sorts  in
          (match uu____2358 with
           | (names,binders,n) ->
               let binders =
                 FStar_All.pipe_right binders (FStar_String.concat " ")  in
               let pats = remove_guard_free pats  in
               let pats_str =
                 match pats with
                 | []::[]|[] -> ""
                 | uu____2386 ->
                     let _0_314 =
                       FStar_All.pipe_right pats
                         (FStar_List.map
                            (fun pats  ->
                               let _0_313 =
                                 let _0_312 =
                                   FStar_List.map
                                     (fun p  ->
                                        let _0_311 = aux n names p  in
                                        FStar_Util.format1 "%s" _0_311) pats
                                    in
                                 FStar_String.concat " " _0_312  in
                               FStar_Util.format1 "\n:pattern (%s)" _0_313))
                        in
                     FStar_All.pipe_right _0_314 (FStar_String.concat "\n")
                  in
               (match (pats, wopt) with
                | ([]::[],None )|([],None ) ->
                    let _0_315 = aux n names body  in
                    FStar_Util.format3 "(%s (%s)\n %s);;no pats\n"
                      (qop_to_string qop) binders _0_315
                | uu____2409 ->
                    let _0_317 = aux n names body  in
                    let _0_316 = weightToSmt wopt  in
                    FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))"
                      (qop_to_string qop) binders _0_317 _0_316 pats_str))
      | Let (es,body) ->
          let uu____2419 =
            FStar_List.fold_left
              (fun uu____2434  ->
                 fun e  ->
                   match uu____2434 with
                   | (names0,binders,n0) ->
                       let nm =
                         let _0_318 = FStar_Util.string_of_int n0  in
                         Prims.strcat "@lb" _0_318  in
                       let names0 = (nm, Term_sort) :: names0  in
                       let b =
                         let _0_319 = aux n names e  in
                         FStar_Util.format2 "(%s %s)" nm _0_319  in
                       (names0, (b :: binders), (n0 + (Prims.parse_int "1"))))
              (names, [], n) es
             in
          (match uu____2419 with
           | (names,binders,n) ->
               let _0_320 = aux n names body  in
               FStar_Util.format2 "(let (%s) %s)"
                 (FStar_String.concat " " binders) _0_320)
    
    and aux n names t =
      let s = aux' n names t  in
      if t.rng <> norng
      then
        let _0_322 = FStar_Range.string_of_range t.rng  in
        let _0_321 = FStar_Range.string_of_use_range t.rng  in
        FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _0_322 _0_321 s
      else s
     in aux (Prims.parse_int "0") [] t
  
let caption_to_string : Prims.string Prims.option -> Prims.string =
  fun uu___87_2495  ->
    match uu___87_2495 with
    | None  -> ""
    | Some c ->
        let uu____2498 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd::[] -> (hd, "")
          | hd::uu____2507 -> (hd, "...")  in
        (match uu____2498 with
         | (hd,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
  
let rec declToSmt : Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_'  in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let _0_323 =
            FStar_All.pipe_right (FStar_Util.splitlines c)
              (fun uu___88_2525  ->
                 match uu___88_2525 with | [] -> "" | h::t -> h)
             in
          FStar_Util.format1 "\n; %s" _0_323
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts  in
          let _0_325 = caption_to_string c  in
          let _0_324 = strSort retsort  in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _0_325 f
            (FStar_String.concat " " l) _0_324
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2545 = name_macro_binders arg_sorts  in
          (match uu____2545 with
           | (names,binders) ->
               let body =
                 let _0_326 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names  in
                 inst _0_326 body  in
               let _0_329 = caption_to_string c  in
               let _0_328 = strSort retsort  in
               let _0_327 = termToSmt body  in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _0_329 f
                 (FStar_String.concat " " binders) _0_328 _0_327)
      | Assume (t,c,Some n) ->
          let _0_331 = caption_to_string c  in
          let _0_330 = termToSmt t  in
          FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _0_331 _0_330
            (escape n)
      | Assume (t,c,None ) ->
          let _0_333 = caption_to_string c  in
          let _0_332 = termToSmt t  in
          FStar_Util.format2 "%s(assert %s)" _0_333 _0_332
      | Eval t ->
          let _0_334 = termToSmt t  in FStar_Util.format1 "(eval %s)" _0_334
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v) -> FStar_Util.format2 "(set-option :%s %s)" s v
      | PrintStats  -> "(get-info :all-statistics)"

and mkPrelude : Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n"
       in
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
        Term_sort, (Prims.parse_int "11"), true)]
       in
    let bcons =
      let _0_336 =
        let _0_335 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right _0_335 (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right _0_336 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let mk_Range_const : term = mkApp ("Range_const", []) norng 
let mk_Term_type : term = mkApp ("Tm_type", []) norng 
let mk_Term_app : term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let mk_Term_uvar : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let _0_339 =
        let _0_338 = let _0_337 = mkInteger' i norng  in [_0_337]  in
        ("Tm_uvar", _0_338)  in
      mkApp _0_339 r
  
let mk_Term_unit : term = mkApp ("Tm_unit", []) norng 
let boxInt : term -> term = fun t  -> mkApp ("BoxInt", [t]) t.rng 
let unboxInt : term -> term = fun t  -> mkApp ("BoxInt_proj_0", [t]) t.rng 
let boxBool : term -> term = fun t  -> mkApp ("BoxBool", [t]) t.rng 
let unboxBool : term -> term = fun t  -> mkApp ("BoxBool_proj_0", [t]) t.rng 
let boxString : term -> term = fun t  -> mkApp ("BoxString", [t]) t.rng 
let unboxString : term -> term =
  fun t  -> mkApp ("BoxString_proj_0", [t]) t.rng 
let boxRef : term -> term = fun t  -> mkApp ("BoxRef", [t]) t.rng 
let unboxRef : term -> term = fun t  -> mkApp ("BoxRef_proj_0", [t]) t.rng 
let boxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | uu____2842 -> Prims.raise FStar_Util.Impos
  
let unboxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____2849 -> Prims.raise FStar_Util.Impos
  
let mk_PreType : term -> term = fun t  -> mkApp ("PreType", [t]) t.rng 
let mk_Valid : term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____2857::t1::t2::[]);
                       freevars = uu____2860; rng = uu____2861;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____2868::t1::t2::[]);
                       freevars = uu____2871; rng = uu____2872;_}::[])
        -> let _0_340 = mkEq (t1, t2) norng  in mkNot _0_340 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____2881; rng = uu____2882;_}::[])
        ->
        let _0_343 =
          let _0_342 = unboxInt t1  in
          let _0_341 = unboxInt t2  in (_0_342, _0_341)  in
        mkLTE _0_343 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____2891; rng = uu____2892;_}::[])
        ->
        let _0_346 =
          let _0_345 = unboxInt t1  in
          let _0_344 = unboxInt t2  in (_0_345, _0_344)  in
        mkLT _0_346 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____2901; rng = uu____2902;_}::[])
        ->
        let _0_349 =
          let _0_348 = unboxInt t1  in
          let _0_347 = unboxInt t2  in (_0_348, _0_347)  in
        mkGTE _0_349 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____2911; rng = uu____2912;_}::[])
        ->
        let _0_352 =
          let _0_351 = unboxInt t1  in
          let _0_350 = unboxInt t2  in (_0_351, _0_350)  in
        mkGT _0_352 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____2921; rng = uu____2922;_}::[])
        ->
        let _0_355 =
          let _0_354 = unboxBool t1  in
          let _0_353 = unboxBool t2  in (_0_354, _0_353)  in
        mkAnd _0_355 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____2931; rng = uu____2932;_}::[])
        ->
        let _0_358 =
          let _0_357 = unboxBool t1  in
          let _0_356 = unboxBool t2  in (_0_357, _0_356)  in
        mkOr _0_358 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t::[]);
                       freevars = uu____2940; rng = uu____2941;_}::[])
        -> let _0_359 = unboxBool t  in mkNot _0_359 t.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___89_2950 = unboxBool t1  in
        {
          tm = (uu___89_2950.tm);
          freevars = (uu___89_2950.freevars);
          rng = (t.rng)
        }
    | uu____2953 -> mkApp ("Valid", [t]) t.rng
  
let mk_HasType : term -> term -> term =
  fun v  -> fun t  -> mkApp ("HasType", [v; t]) t.rng 
let mk_HasTypeZ : term -> term -> term =
  fun v  -> fun t  -> mkApp ("HasTypeZ", [v; t]) t.rng 
let mk_IsTyped : term -> term = fun v  -> mkApp ("IsTyped", [v]) norng 
let mk_HasTypeFuel : term -> term -> term -> term =
  fun f  ->
    fun v  ->
      fun t  ->
        let uu____2982 = FStar_Options.unthrottle_inductives ()  in
        if uu____2982
        then mk_HasType v t
        else mkApp ("HasTypeFuel", [f; v; t]) t.rng
  
let mk_HasTypeWithFuel : term Prims.option -> term -> term -> term =
  fun f  ->
    fun v  ->
      fun t  ->
        match f with
        | None  -> mk_HasType v t
        | Some f -> mk_HasTypeFuel f v t
  
let mk_Destruct : term -> FStar_Range.range -> term =
  fun v  -> mkApp ("Destruct", [v]) 
let mk_Rank : term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x]) 
let mk_tester : Prims.string -> term -> term =
  fun n  -> fun t  -> mkApp ((Prims.strcat "is-" n), [t]) t.rng 
let mk_ApplyTF : term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng 
let mk_ApplyTT : term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r 
let mk_String_const : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let _0_362 =
        let _0_361 = let _0_360 = mkInteger' i norng  in [_0_360]  in
        ("FString_const", _0_361)  in
      mkApp _0_362 r
  
let mk_Precedes : term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let _0_363 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right _0_363 mk_Valid
  
let mk_LexCons : term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec n_fuel : Prims.int -> term =
  fun n  ->
    if n = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let _0_366 =
         let _0_365 =
           let _0_364 = n_fuel (n - (Prims.parse_int "1"))  in [_0_364]  in
         ("SFuel", _0_365)  in
       mkApp _0_366 norng)
  
let fuel_2 : term = n_fuel (Prims.parse_int "2") 
let fuel_100 : term = n_fuel (Prims.parse_int "100") 
let mk_and_opt :
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
  
let mk_and_opt_l :
  term Prims.option Prims.list -> FStar_Range.range -> term Prims.option =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        None
  
let mk_and_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let _0_367 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l _0_367
  
let mk_or_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let _0_368 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l _0_368
  
let mk_haseq : term -> term =
  fun t  -> mk_Valid (mkApp ("Prims.hasEq", [t]) t.rng) 
let rec print_smt_term : term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n -> FStar_Util.format1 "(Integer %s)" n
    | BoundV n ->
        let _0_369 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "(BoundV %s)" _0_369
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (Prims.fst fv)
    | App (op,l) ->
        let _0_370 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" (op_to_string op) _0_370
    | Labeled (t,r1,r2) ->
        let _0_371 = print_smt_term t  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 _0_371
    | LblPos (t,s) ->
        let _0_372 = print_smt_term t  in
        FStar_Util.format2 "(LblPos %s %s)" s _0_372
    | Quant (qop,l,uu____3161,uu____3162,t) ->
        let _0_374 = print_smt_term_list_list l  in
        let _0_373 = print_smt_term t  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _0_374 _0_373
    | Let (es,body) ->
        let _0_376 = print_smt_term_list es  in
        let _0_375 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" _0_376 _0_375

and print_smt_term_list : term Prims.list -> Prims.string =
  fun l  ->
    let _0_377 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right _0_377 (FStar_String.concat " ")

and print_smt_term_list_list : term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l  ->
           let _0_380 =
             let _0_379 =
               let _0_378 = print_smt_term_list l  in
               Prims.strcat _0_378 " ] "  in
             Prims.strcat "; [ " _0_379  in
           Prims.strcat s _0_380) "" l
