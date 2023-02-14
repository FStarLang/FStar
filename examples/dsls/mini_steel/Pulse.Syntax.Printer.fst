module Pulse.Syntax.Printer
open FStar.Printf
open Pulse.Syntax
module R = FStar.Reflection
let name_to_string (f:R.name) = String.concat "." f

let dbg_printing : bool = true

let constant_to_string = function
  | Unit -> "()"
  | Bool true -> "true"
  | Bool false -> "true"  
  | Int i -> sprintf "%d" i

let rec universe_to_string (n:nat) (u:universe) 
  : Tot string (decreases u) = 
  match u with
  | U_zero -> sprintf "%d" n
  | U_succ u -> universe_to_string (n + 1) u
  | U_var x -> if n = 0 then x else sprintf "(%s + %d)" x n
  | U_max u0 u1 -> 
    let r = sprintf "(max %s %s)" (universe_to_string 0 u0) (universe_to_string 0 u1) in
    if n = 0 then r else sprintf "%s + %d" r n

let univ_to_string u = sprintf "u#%s" (universe_to_string 0 u)
let qual_to_string = function
  | None -> ""
  | Some Implicit -> "#"
  
let rec term_to_string (t:term)
  : string
  = match t with
    | Tm_BVar x ->
      if dbg_printing
      then sprintf "%s@%d" x.bv_ppname x.bv_index
      else x.bv_ppname
    | Tm_Var x ->
      if dbg_printing
      then sprintf "%s#%d" x.nm_ppname x.nm_index
      else x.nm_ppname
    | Tm_FVar f -> name_to_string f
    | Tm_UInst f us -> sprintf "%s %s" (name_to_string f) (String.concat " " (List.Tot.map univ_to_string us))
    | Tm_Constant c -> constant_to_string c
    | Tm_Refine b phi ->
      sprintf "%s:%s{%s}"
              b.binder_ppname
              (term_to_string b.binder_ty)
              (term_to_string phi)
    | Tm_Abs b q pre_hint body post ->
      sprintf "(fun (%s%s) {%s} {_.%s} -> %s)"
              (qual_to_string q)
              (binder_to_string b)
              (term_to_string pre_hint)
              (match post with
               | None -> "<none>"
               | Some post -> sprintf "%s" (term_to_string post))
              (term_to_string body)

    | Tm_PureApp head q arg ->
      sprintf "(%s %s%s)" 
        (term_to_string head)
        (qual_to_string q)
        (term_to_string arg)
      
    | Tm_Let t e1 e2 ->
      sprintf "let _ : %s = %s in %s"
        (term_to_string t)
        (term_to_string e1)
        (term_to_string e2)        
      
    | Tm_STApp head q arg ->
      sprintf "(%s%s %s%s)"
        (if dbg_printing then "<stapp>" else "")
        (term_to_string head)
        (qual_to_string q)
        (term_to_string arg)
        
    | Tm_Bind e1 e2 ->
      sprintf "bind _ = %s in %s"
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
                          
    | Tm_Arrow b q c ->
      sprintf "%s%s -> %s"
        (qual_to_string q)
        (binder_to_string b)
        (comp_to_string c)
        
    | Tm_Type _ ->
      "Type u#_"
      
    | Tm_VProp ->
      "vprop"

    | Tm_Inames -> "inames"

    | Tm_EmpInames -> "emp_inames"
      
    | Tm_If b t e _ ->
      sprintf "(if %s then %s else %s)"
        (term_to_string b)
        (term_to_string t)
        (term_to_string e)        

    | Tm_ElimExists t ->
      sprintf "elim_exists %s"
        (term_to_string t)

    | Tm_IntroExists t e ->
      sprintf "intro_exists %s %s"
        (term_to_string t)
        (term_to_string e)

    | Tm_UVar n -> sprintf "?u_%d" n

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

  | C_STAtomic inames s ->
    sprintf "STAtomic %s %s %s %s"
      (term_to_string inames)
      (term_to_string s.res)
      (term_to_string s.pre)
      (term_to_string s.post)

  | C_STGhost inames s ->
    sprintf "STGhost %s %s %s %s"
      (term_to_string inames)
      (term_to_string s.res)
      (term_to_string s.pre)
      (term_to_string s.post)
