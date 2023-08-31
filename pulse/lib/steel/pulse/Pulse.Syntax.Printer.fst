module Pulse.Syntax.Printer
open FStar.Printf
open Pulse.Syntax.Base

module L = FStar.List.Tot

module T = FStar.Tactics.V2
module Un = FStar.Sealed
module R = FStar.Reflection.V2

let tot_or_ghost_to_string = function
  | T.E_Total -> "total"
  | T.E_Ghost -> "ghost"


let name_to_string (f:R.name) = String.concat "." f

let dbg_printing : bool = true

// let constant_to_string = function
//   | Unit -> "()"
//   | Bool true -> "true"
//   | Bool false -> "false"
//   | Int i -> sprintf "%d" i

let rec universe_to_string (n:nat) (u:universe) 
  : Tot string (decreases u) =
  let open R in
  match inspect_universe u with
  | Uv_Unk -> "_"
  | Uv_Zero -> sprintf "%d" n
  | Uv_Succ u -> universe_to_string (n + 1) u
  | Uv_BVar x -> if n = 0 then sprintf "%d" x else sprintf "(%d + %d)" x n
  | Uv_Max us ->
    let r = "(max _)" in
    // sprintf "(max %s %s)" (universe_to_string 0 u0) (universe_to_string 0 u1) in
    if n = 0 then r else sprintf "%s + %d" r n
  | _ -> sprintf "<univ>"

let univ_to_string u = sprintf "u#%s" (universe_to_string 0 u)
let qual_to_string = function
  | None -> ""
  | Some Implicit -> "#"

let indent (level:string) = level ^ "\t"
    
let rec term_to_string' (level:string) (t:term)
  : T.Tac string
  = match t.t with
    | Tm_Emp -> "emp"

    | Tm_Pure p ->
      sprintf "pure (\n%s%s)" 
        (indent level)
        (term_to_string' (indent level) p)
      
    | Tm_Star p1 p2 ->
      sprintf "%s ** \n%s%s" 
        (term_to_string' level p1)
        level
        (term_to_string' level p2)
                          
    | Tm_ExistsSL _ b body ->
      sprintf "(exists (%s:%s).\n%s%s)"
              (T.unseal b.binder_ppname.name)
              (term_to_string' (indent level) b.binder_ty)
              level
              (term_to_string' (indent level) body)

    | Tm_ForallSL u b body ->
      sprintf "(forall (%s:%s).\n%s%s)"
              (T.unseal b.binder_ppname.name)
              (term_to_string' (indent level) b.binder_ty)
              level
              (term_to_string' (indent level) body)
                          
    | Tm_VProp -> "vprop"
    | Tm_Inames -> "inames"
    | Tm_EmpInames -> "emp_inames"
    | Tm_Unknown -> "_"
    | Tm_FStar t ->
      T.term_to_string t
let term_to_string t = term_to_string' "" t

let binder_to_string (b:binder)
  : T.Tac string
  = sprintf "%s:%s" 
            (T.unseal b.binder_ppname.name)
            (term_to_string b.binder_ty)

let ctag_to_string = function
  | STT -> "ST"
  | STT_Atomic -> "STAtomic"
  | STT_Ghost -> "STGhost"

let comp_to_string (c:comp)
  : T.Tac string
  = match c with
    | C_Tot t -> 
      sprintf "Tot %s" (term_to_string t)
      
    | C_ST s ->
      sprintf "stt %s (requires\n%s) (ensures\n%s)"
              (term_to_string s.res)
              (term_to_string s.pre)
              (term_to_string s.post)

    | C_STAtomic inames s ->
      sprintf "stt_atomic %s %s (requires\n%s) (ensures\n%s)"
              (term_to_string inames)
              (term_to_string s.res)
              (term_to_string s.pre)
              (term_to_string s.post)

    | C_STGhost inames s ->
      sprintf "stt_atomic %s %s (requires\n%s) (ensures\n%s)"
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

let rec st_term_to_string' (level:string) (t:st_term)
  : T.Tac string
  = match t.term with
    | Tm_Return { ctag; insert_eq; term } ->
      sprintf "return_%s%s %s"
        (match ctag with
         | STT -> "stt"
         | STT_Atomic -> "stt_atomic"
         | STT_Ghost -> "stt_ghost")
        (if insert_eq then "" else "_noeq")
        (term_to_string term)
      
    | Tm_STApp {head; arg_qual; arg } ->
      sprintf "(%s%s %s%s)"
        (if dbg_printing then "<stapp>" else "")
        (term_to_string head)
        (qual_to_string arg_qual)
        (term_to_string arg)
        
    | Tm_Bind { binder; head; body } ->
      // if T.unseal binder.binder_ppname.name = "_"
      // then sprintf "%s;\n%s%s" 
      //              (st_term_to_string' level head)
      //              level
      //              (st_term_to_string' level body)                   
      // else (
        sprintf "let %s = %s;\n%s%s"
          (binder_to_string binder)      
          (st_term_to_string' level head)
          level
          (st_term_to_string' level body)
      // )

    | Tm_TotBind { head; binder; body } ->
      sprintf "let tot %s = %s;\n%s%s"
        (binder_to_string binder)
        (term_to_string head)
        level
        (st_term_to_string' level body)
  
    | Tm_Abs { b; q; ascription=c; body } ->
      sprintf "(fun (%s%s)\n%s\n {\n%s%s\n}"
              (qual_to_string q)
              (binder_to_string b)
              (comp_to_string c)
              (indent level)
              (st_term_to_string' (indent level) body)

    | Tm_If { b; then_; else_ } ->
      sprintf "if (%s)\n%s{\n%s%s\n%s}\n%selse\n%s{\n%s%s\n%s}"
        (term_to_string b)
        level
        (indent level)
        (st_term_to_string' (indent level) then_)
        level
        level
        level
        (indent level)
        (st_term_to_string' (indent level) else_)
        level

    | Tm_Match {sc; brs} ->
      sprintf "match (%s) with %s"
        (term_to_string sc)
        (branches_to_string brs)

    | Tm_IntroPure { p } ->
      sprintf "introduce pure (\n%s%s)"
        (indent level)
        (term_to_string' (indent level) p)

    | Tm_ElimExists { p } ->
      sprintf "elim_exists %s"
        (term_to_string p)

    | Tm_IntroExists { p; witnesses } ->
      sprintf "introduce\n%s%s\n%swith %s"
        (indent level)
        (term_to_string' (indent level) p)
        level
        (term_list_to_string " " witnesses)

    | Tm_While { invariant; condition; body } ->
      sprintf "while (%s)\n%sinvariant %s\n%s{\n%s%s\n%s}"
        (st_term_to_string' level condition)
        level
        (term_to_string invariant)
        level
        (indent level)
        (st_term_to_string' (indent level) body)
        level

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      sprintf "par (<%s> (%s) <%s) (<%s> (%s) <%s)"
        (term_to_string pre1)
        (st_term_to_string' level body1)
        (term_to_string post1)
        (term_to_string pre2)
        (st_term_to_string' level body2)
        (term_to_string post2)

    | Tm_Rewrite { t1; t2 } ->
       sprintf "rewrite %s %s"
        (term_to_string t1)
        (term_to_string t2)

    | Tm_WithLocal { binder; initializer; body } ->
      sprintf "let mut %s = %s;\n%s%s"
        (binder_to_string binder)
        (term_to_string initializer)
        level
        (st_term_to_string' level body)

    | Tm_Admit { ctag; u; typ; post } ->
      sprintf "%s<%s> %s%s"
        (match ctag with
         | STT -> "stt_admit"
         | STT_Atomic -> "stt_atomic_admit"
         | STT_Ghost -> "stt_ghost_admit")
        (universe_to_string 0 u)
        (term_to_string typ)
        (match post with
         | None -> ""
         | Some post -> sprintf " %s" (term_to_string post))

    | Tm_ProofHintWithBinders { binders; hint_type; t} ->
      let with_prefix =
        match binders with
        | [] -> ""
        | _ -> sprintf "with %s." (String.concat " " (T.map binder_to_string binders))
      in
      let names_to_string = function
        | None -> ""
        | Some l -> sprintf " [%s]" (String.concat "; " l)
      in
      let ht, p =
        match hint_type with
        | ASSERT { p } -> "assert", term_to_string p
        | UNFOLD { names; p } -> sprintf "unfold%s" (names_to_string names), term_to_string p
        | FOLD { names; p } -> sprintf "fold%s" (names_to_string names), term_to_string p
        | RENAME { pairs; goal } ->
          sprintf "rename %s"
            (String.concat ", "
              (T.map
                (fun (x, y) -> sprintf "%s as %s" (term_to_string x) (term_to_string y))
              pairs)),
            (match goal with
            | None -> ""
            | Some t -> sprintf " in %s" (term_to_string t))
      in
      sprintf "%s %s %s; %s" with_prefix ht p
        (st_term_to_string' level t)

and branches_to_string brs : T.Tac _ =
  match brs with
  | [] -> ""
  | b::bs -> branch_to_string b ^ branches_to_string bs

and branch_to_string br : T.Tac _ =
  let (pat, e) = br in
  st_term_to_string' "" e

let st_term_to_string t = st_term_to_string' "" t

let tag_of_term (t:term) =
  match t.t with
  | Tm_Emp -> "Tm_Emp"
  | Tm_Pure _ -> "Tm_Pure"
  | Tm_Star _ _ -> "Tm_Star"
  | Tm_ExistsSL _ _ _ -> "Tm_ExistsSL"
  | Tm_ForallSL _ _ _ -> "Tm_ForallSL"
  | Tm_VProp -> "Tm_VProp"
  | Tm_Inames -> "Tm_Inames"
  | Tm_EmpInames -> "Tm_EmpInames"
  | Tm_Unknown -> "Tm_Unknown"
  | Tm_FStar _ -> "Tm_FStar"

let tag_of_st_term (t:st_term) =
  match t.term with
  | Tm_Return _ -> "Tm_Return"
  | Tm_Abs _ -> "Tm_Abs"
  | Tm_STApp _ -> "Tm_STApp"
  | Tm_Bind _ -> "Tm_Bind"
  | Tm_TotBind _ -> "Tm_TotBind"
  | Tm_If _ -> "Tm_If"
  | Tm_Match _ -> "Tm_Match"
  | Tm_IntroPure _ -> "Tm_IntroPure"
  | Tm_ElimExists _ -> "Tm_ElimExists"
  | Tm_IntroExists _ -> "Tm_IntroExists"
  | Tm_While _ -> "Tm_While"
  | Tm_Par _ -> "Tm_Par"
  | Tm_WithLocal _ -> "Tm_WithLocal"
  | Tm_Rewrite _ -> "Tm_Rewrite"
  | Tm_Admit _ -> "Tm_Admit"
  | Tm_ProofHintWithBinders _ -> "Tm_ProofHintWithBinders"

let tag_of_comp (c:comp) : T.Tac string =
  match c with
  | C_Tot _ -> "Total"
  | C_ST _ -> "ST"
  | C_STAtomic i _ ->
    Printf.sprintf "Atomic %s" (term_to_string i)
  | C_STGhost i _ ->
    Printf.sprintf "Ghost %s" (term_to_string i)
    
let rec print_st_head (t:st_term)
  : Tot string (decreases t) =
  match t.term with
  | Tm_Abs _  -> "Abs"
  | Tm_Return p -> print_head p.term
  | Tm_Bind _ -> "Bind"
  | Tm_TotBind _ -> "TotBind"
  | Tm_If _ -> "If"
  | Tm_Match _ -> "Match"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroPure _ -> "IntroPure"
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"  
  | Tm_ProofHintWithBinders _ -> "AssertWithBinders"
and print_head (t:term) =
  match t with
  // | Tm_FVar fv
  // | Tm_UInst fv _ -> String.concat "." fv.fv_name
  // | Tm_PureApp head _ _ -> print_head head
  | _ -> "<pure term>"


let rec print_skel (t:st_term) = 
  match t.term with
  | Tm_Abs { body }  -> Printf.sprintf "(fun _ -> %s)" (print_skel body)
  | Tm_Return { term = p } -> print_head p
  | Tm_Bind { head=e1; body=e2 } -> Printf.sprintf "(Bind %s %s)" (print_skel e1) (print_skel e2)
  | Tm_TotBind { body=e2 } -> Printf.sprintf "(TotBind _ %s)" (print_skel e2)
  | Tm_If _ -> "If"
  | Tm_Match _ -> "Match"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroPure _ -> "IntroPure"
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"
  | Tm_ProofHintWithBinders _ -> "AssertWithBinders"
