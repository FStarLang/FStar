module Pulse.Syntax.Printer
open FStar.Printf
open Pulse.Syntax
module T = FStar.Tactics
module Un = FStar.Sealed
module R = FStar.Reflection
let name_to_string (f:R.name) = String.concat "." f

let dbg_printing : bool = true

let constant_to_string = function
  | Unit -> "()"
  | Bool true -> "true"
  | Bool false -> "false"
  | Int i -> sprintf "%d" i

let rec universe_to_string (n:nat) (u:universe) 
  : Tot string (decreases u) = 
  match u with
  | U_unknown -> "_"
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
  : T.Tac string
  = match t with
    | Tm_BVar x ->
      if dbg_printing
      then sprintf "%s@%d" (T.unseal x.bv_ppname) x.bv_index
      else T.unseal x.bv_ppname
    | Tm_Var x ->
      if dbg_printing
      then sprintf "%s#%d" (T.unseal x.nm_ppname) x.nm_index
      else T.unseal x.nm_ppname
    | Tm_FVar f -> name_to_string f.fv_name
    | Tm_UInst f us -> sprintf "%s %s" (name_to_string f.fv_name) (String.concat " " (List.Tot.map univ_to_string us))
    | Tm_Constant c -> constant_to_string c
    | Tm_Refine b phi ->
      sprintf "%s:%s{%s}"
              (T.unseal b.binder_ppname)
              (term_to_string b.binder_ty)
              (term_to_string phi)

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
      
    | Tm_Emp -> "emp"
    | Tm_Pure p -> sprintf "pure %s" (term_to_string p)
    | Tm_Star p1 p2 ->
      sprintf "(%s * %s)" (term_to_string p1)
                          (term_to_string p2)
                          
    | Tm_ExistsSL u t body _ ->
      sprintf "(exists<%s> (_:%s). %s)"
              (universe_to_string 0 u)
              (term_to_string t)
              (term_to_string body)

    | Tm_ForallSL u t body ->
      sprintf "(forall<%s> (_:%s). %s)"
              (universe_to_string 0 u)
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
      
    | Tm_UVar n -> sprintf "?u_%d" n

    | Tm_Unknown -> "_"
    
    | Tm_FStar t ->
      T.term_to_string t
      
and binder_to_string (b:binder)
  : T.Tac string
  = sprintf "%s:%s" 
            (T.unseal b.binder_ppname)
            (term_to_string b.binder_ty)

and comp_to_string (c:comp)
  : T.Tac string
  = match c with
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

let term_opt_to_string (t:option term)
  : T.Tac string
  = match t with
    | None -> ""
    | Some t -> term_to_string t

let term_list_to_string (sep:string) (t:list term)
  : T.Tac string
  = String.concat sep (T.map term_to_string t)

let rec st_term_to_string (t:st_term)
  : T.Tac string
  = match t with
    | Tm_Return c use_eq t ->
      sprintf "return_%s%s %s"
        (match c with
         | STT -> "stt"
         | STT_Atomic -> "stt_atomic"
         | STT_Ghost -> "stt_ghost")
        (if use_eq then "" else "_noeq")
        (term_to_string t)
      
    | Tm_STApp head q arg ->
      sprintf "(%s%s %s%s)"
        (if dbg_printing then "<stapp>" else "")
        (term_to_string head)
        (qual_to_string q)
        (term_to_string arg)
        
    | Tm_Bind e1 e2 ->
      sprintf "bind _ = %s in %s"
        (st_term_to_string e1)
        (st_term_to_string e2)        
  
    | Tm_Abs b q pre_hint body post ->
      sprintf "(fun (%s%s) {%s} {_.%s} -> %s)"
              (qual_to_string q)
              (binder_to_string b)
              (term_opt_to_string pre_hint)
              (term_opt_to_string post)
              (st_term_to_string body)

    | Tm_If b t e _ ->
      sprintf "(if %s then %s else %s)"
        (term_to_string b)
        (st_term_to_string t)
        (st_term_to_string e)        

    | Tm_ElimExists t ->
      sprintf "elim_exists %s"
        (term_to_string t)

    | Tm_IntroExists false t e ->
      sprintf "intro_exists %s %s"
        (term_to_string t)
        (term_list_to_string " " e)

    | Tm_IntroExists true t e ->
      sprintf "intro_exists_erased %s %s"
        (term_to_string t)
        (term_list_to_string " " e)

    | Tm_While inv cond body ->
      sprintf "while<%s> (%s) {%s}"
        (term_to_string inv)
        (st_term_to_string cond)
        (st_term_to_string body)

    | Tm_Par preL eL postL preR eR postR ->
      sprintf "par (<%s> (%s) <%s) (<%s> (%s) <%s)"
        (term_to_string preL)
        (st_term_to_string eL)
        (term_to_string postL)
        (term_to_string preR)
        (st_term_to_string eR)
        (term_to_string postR)

				| Tm_Rewrite p q ->
				  sprintf "rewrite %s %s"
						  (term_to_string p)
								(term_to_string q)

    | Tm_WithLocal init e ->
      sprintf "let mut _ = %s in %s"
        (term_to_string init)
        (st_term_to_string e)

    | Tm_Admit c u t post ->
      sprintf "%s<%s> %s%s"
        (match c with
         | STT -> "stt_admit"
         | STT_Atomic -> "stt_atomic_admit"
         | STT_Ghost -> "stt_ghost_admit")
        (universe_to_string 0 u)
        (term_to_string t)
        (match post with
         | None -> ""
         | Some post -> sprintf " %s" (term_to_string post))

    | Tm_Protect t ->
      st_term_to_string t
