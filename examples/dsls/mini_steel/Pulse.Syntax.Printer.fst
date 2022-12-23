module Pulse.Syntax.Printer
open FStar.Printf
open Pulse.Syntax
module R = FStar.Reflection
let name_to_string (f:R.name) = String.concat "." f

let constant_to_string = function
  | Unit -> "()"
  | Bool true -> "true"
  | Bool false -> "true"  
  | Int i -> sprintf "%d" i

let rec term_to_string (t:term)
  : string
  = match t with
    | Tm_BVar x -> x.bv_ppname
    | Tm_Var x -> x.nm_ppname
    | Tm_FVar f -> name_to_string f
    | Tm_Constant c -> constant_to_string c
    | Tm_Refine b phi ->
      sprintf "%s:%s{%s}"
              b.binder_ppname
              (term_to_string b.binder_ty)
              (term_to_string phi)
    | Tm_Abs b pre_hint body post ->
      sprintf "(fun (%s) {%s} -> %s%s)"
              (binder_to_string b)
              (term_to_string pre_hint)
              (term_to_string body)
              (match post with
               | None -> ""
               | Some post -> sprintf " {%s}" (term_to_string post))

    | Tm_PureApp head arg ->
      sprintf "(%s %s)" (term_to_string head) (term_to_string arg)
      
    | Tm_Let t e1 e2 ->
      sprintf "let _ : %s = %s in %s"
        (term_to_string t)
        (term_to_string e1)
        (term_to_string e2)        
      
    | Tm_STApp head arg ->
      sprintf "(%s{%s})"
        (term_to_string head)
        (term_to_string arg)
        
    | Tm_Bind t e1 e2 ->
      sprintf "bind _ : %s = %s in %s"
        (term_to_string t)
        (term_to_string e1)
        (term_to_string e2)        

    | Tm_Emp -> "emp"
    | Tm_Pure p -> sprintf "pure %s" (term_to_string p)
    | Tm_Star p1 p2 ->
      sprintf "(%s * %s)" (term_to_string p1)
                          (term_to_string p2)
                          
    | Tm_ExistsSL t body ->
      sprintf "(exists (_:%s). %s)"
              (term_to_string t)
              (term_to_string body)

    | Tm_ForallSL t body ->
      sprintf "(forall (_:%s). %s)"
              (term_to_string t)
              (term_to_string body)
                          
    | Tm_Arrow b c ->
      sprintf "%s -> %s"
        (binder_to_string b)
        (comp_to_string c)
        
    | Tm_Type _ ->
      "Type u#_"
      
    | Tm_VProp ->
      "vprop"
      
    | Tm_If b t e ->
      sprintf "(if %s then %s else %s)"
        (term_to_string b)
        (term_to_string t)
        (term_to_string e)        

and binder_to_string b =
  sprintf "%s:%s" 
    b.binder_ppname
    (term_to_string b.binder_ty)

and comp_to_string c =
  match c with
  | C_Tot t -> 
    sprintf "Tot %s" (term_to_string t)
    
  | C_ST s ->
    sprintf "ST %s %s %s"
      (term_to_string s.res)
      (term_to_string s.pre)
      (term_to_string s.post)
