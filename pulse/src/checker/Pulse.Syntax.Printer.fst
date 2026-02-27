(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Syntax.Printer
open FStar.Printf
open Pulse.Syntax


module T = FStar.Tactics.V2
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
  | Some TcArg -> "#[tcresolve]"
  | Some (Meta t) -> sprintf "#[%s]" (T.term_to_string t)

let indent (level:string) = level ^ "\t"

let rec collect_binders (until: term_view -> bool) (t:term) : list binder & term =
  let tv = inspect_term t in
  if not (until tv) then [], t
  else (
    match tv with
    | Tm_ExistsSL _ b body
    | Tm_ForallSL _ b body -> 
      let bs, t = collect_binders until body in
      b::bs, t
    | _ -> [], t
  )

let rec binder_to_string_paren (b:binder)
  : T.Tac string
  = sprintf "(%s%s:%s)"
            (match T.unseal b.binder_attrs with
             | [] -> ""
             | l -> sprintf "[@@@ %s] " (String.concat ";" (T.map (term_to_string' "") l)))
            (T.unseal b.binder_ppname.name)
            (term_to_string' "" b.binder_ty)

and term_to_string' (level:string) (t:term) : T.Tac string
  = match inspect_term t with
    | Tm_Emp -> "emp"

    | Tm_IsUnreachable -> "is_unreachable"

    | Tm_Pure p ->
      sprintf "pure (%s)" 
        (term_to_string' (indent level) p)
      
    | Tm_Star p1 p2 ->
      sprintf "%s ** \n%s%s" 
        (term_to_string' level p1)
        level
        (term_to_string' level p2)

    | Tm_WithPure p n v ->
      sprintf "(with_pure %s fun _ ->\n%s%s)"
              (term_to_string' (indent level) p)
              level
              (term_to_string' (indent level) v)
                      
    | Tm_ExistsSL _ _ _ ->
      let bs, body = collect_binders Tm_ExistsSL? t in
      sprintf "(exists* %s.\n%s%s)"
              (T.map binder_to_string_paren bs |> String.concat " ")
              level
              (term_to_string' (indent level) body)

    | Tm_ForallSL u b body ->
      let bs, body = collect_binders Tm_ForallSL? t in
      sprintf "(forall* %s.\n%s%s)"
              (T.map binder_to_string_paren bs |> String.concat " ")
              level
              (term_to_string' (indent level) body)
                          
    | Tm_SLProp -> "slprop"
    | Tm_Inames -> "inames"
    | Tm_EmpInames -> "emp_inames"
    | Tm_Unknown -> "_"
    | Tm_Inv i p ->
      sprintf "inv %s %s"
        (term_to_string' level i)
        (term_to_string' level p)
    | Tm_FStar t -> T.term_to_string t

let term_to_string t = term_to_string' "" t

let star_doc = doc_of_string "**"

val fold_right1: ('a -> 'a -> T.Tac 'a) -> list 'a -> T.Tac 'a
let rec fold_right1 f l = match l with
  | [] -> T.fail "fold_right1: empty list"
  | [x] -> x
  | hd::tl -> f hd (fold_right1 f tl)

let should_paren_term (t:term) : T.Tac bool =
  match t with
  | T.Tv_Match _ _ _ -> true
  | _ -> false

let rec binder_to_doc b : T.Tac document =
  parens (doc_of_string (T.unseal b.binder_ppname.name)
          ^^ doc_of_string ":"
          ^^ term_to_doc b.binder_ty)

and term_to_doc t : T.Tac document
  = match inspect_term t with
    | Tm_Emp -> doc_of_string "emp"
    | Tm_IsUnreachable -> doc_of_string "is_unreachable"

    | Tm_Pure p -> doc_of_string "pure " ^^ parens (term_to_doc p)
    | Tm_Star _ _ ->
      (* We gather all the components of the star so we can
         print in fully-flat or fully-unflattened style (otherwise
          we could get most of the slprops in different lines, except for
          one or two lines which have >1, which is misleading). See #96.
          Some callers to this module also canonicalize the expression
          to put the slprops in order, but we MUST NOT do that here,
          since we are recursively called on arguments,
          and we must not confound pledge p (q ** r) with pledge p (r ** q),
          etc. *)
      let components = slprop_as_list t in
      let term_to_doc_paren (t:term) : T.Tac document =
        if should_paren_term t
        then parens (term_to_doc t)
        else term_to_doc t
      in
      let docs = T.map term_to_doc_paren components in
      (* This makes sure to either print everything on a single line
      or break after every **. The doc_of_string is a non-breakable space,
      the one introduced by ^/^ is breakable. *)
      group <|
        fold_right1 (fun p q -> (p ^^ doc_of_string " " ^^ star_doc) ^/^ q) docs
    
    | Tm_WithPure p n v ->
      parens <|
        prefix 2 1 (prefix 2 1 (doc_of_string "with_pure") (parens (term_to_doc p)
            ^/^ doc_of_string "fun _ ->"))
          (term_to_doc v)

    | Tm_ExistsSL _ _ _ ->
      let bs, body = collect_binders Tm_ExistsSL? t in
      let bs_doc = align (group (separate (doc_of_string " ") (T.map binder_to_doc bs))) in
      parens <|
        prefix 2 1 (prefix 2 1 (doc_of_string "exists*") bs_doc ^^ dot)
                   (term_to_doc body)
      // parens (doc_of_string "exists*" ^/^ (separate (doc_of_string " ") (T.map binder_to_doc bs))
      //         ^^ doc_of_string "."
      //         ^/^ term_to_doc body)

    | Tm_ForallSL _ _ _ ->
      let bs, body = collect_binders Tm_ForallSL? t in
      let bs_doc = align (group (separate (doc_of_string " ") (T.map binder_to_doc bs))) in
      parens <|
        prefix 2 1 (prefix 2 1 (doc_of_string "forall*") bs_doc ^^ dot)
                   (term_to_doc body)

    | Tm_SLProp -> doc_of_string "slprop"
    | Tm_Inames -> doc_of_string "inames"
    | Tm_EmpInames -> doc_of_string "emp_inames"
    | Tm_Inv i p ->
      doc_of_string "inv " ^^
        term_to_doc i ^^
        doc_of_string " " ^^
        parens (term_to_doc p)

    | Tm_Unknown -> doc_of_string "_"
    | Tm_FStar t -> T.term_to_doc t

let binder_to_string (b:binder)
  : T.Tac string
  = sprintf "%s%s:%s"
            (match T.unseal b.binder_attrs with
             | [] -> ""
             | l -> sprintf "[@@@ %s] " (String.concat ";" (T.map (term_to_string' "") l)))
            (T.unseal b.binder_ppname.name)
            (term_to_string b.binder_ty)

let ctag_to_string = function
  | STT -> "ST"
  | STT_Atomic -> "STAtomic"
  | STT_Ghost -> "STGhost"

let observability_to_string =
  function
  | Observable -> "Observable"
  | Neutral -> "Neutral"

let effect_annot_to_string = function
  | EffectAnnotSTT -> "stt"
  | EffectAnnotGhost { opens } -> sprintf "stt_ghost %s" (term_to_string opens)
  | EffectAnnotAtomic { opens } -> sprintf "stt_atomic %s" (term_to_string opens)
  | EffectAnnotAtomicOrGhost { opens } -> sprintf "stt_atomic_or_ghost %s" (term_to_string opens)  

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

    | C_STAtomic inames obs s ->
      sprintf "stt_atomic %s #%s %s (requires\n%s) (ensures\n%s)"
              (term_to_string s.res)
              (observability_to_string obs)
              (term_to_string inames)
              (term_to_string s.pre)
              (term_to_string s.post)

    | C_STGhost inames s ->
      sprintf "stt_ghost %s %s (requires\n%s) (ensures\n%s)"
              (term_to_string s.res)
              (term_to_string inames)
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
    | Tm_Return { insert_eq; term } ->
      sprintf "return%s %s"
        (if insert_eq then "" else "_noeq")
        (term_to_string term)

    | Tm_ST { t; args } ->
      sprintf "%s%s%s"
        (if dbg_printing then "<st>" else "")
        (term_to_string t)
        (T.fold_left (fun acc arg -> acc ^ " " ^ st_term_to_string' level arg) "" args)
        
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
      sprintf "(fun (%s%s)\n%s\n ({\n%s%s\n}%s)"
              (qual_to_string q)
              (binder_to_string b)
              (match c.annotated with | None -> "" | Some c -> comp_to_string c)
              (indent level)
              (st_term_to_string' (indent level) body)
              (match c.elaborated with | None -> "" | Some c -> " <: " ^ comp_to_string c)

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

    | Tm_NuWhile { invariant; meas; condition; body } ->
      sprintf "nuwhile (%s)\n%sinvariant %s\n%s%s{\n%s%s\n%s}"
        (st_term_to_string' level condition)
        level
        (term_to_string invariant)
        level
        (match meas with | Some d -> sprintf "decreases %s\n%s" (term_to_string d) level | None -> "")
        (indent level)
        (st_term_to_string' (indent level) body)
        level

    | Tm_Rewrite { t1; t2; tac_opt } ->
       sprintf "rewrite %s as %s (with %s)"
        (term_to_string t1)
        (term_to_string t2)
        (match tac_opt with | None -> "no tactic" | Some tac -> term_to_string tac)

    | Tm_WithLocal { binder; initializer; body } ->
      sprintf "let mut %s = %s;\n%s%s"
        (binder_to_string binder)
        (term_opt_to_string initializer)
        level
        (st_term_to_string' level body)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      sprintf "let mut %s = [| %s; %s |]\n%s%s"
        (binder_to_string binder)
        (term_opt_to_string initializer)
        (term_to_string length)
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

    | Tm_Unreachable {c} -> sprintf "unreachable #%s ()" (comp_to_string c)

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
        | RENAME { pairs; goal; tac_opt } ->
          sprintf "rewrite each %s (with %s)"
            (String.concat ", "
              (T.map
                (fun (x, y) -> sprintf "%s as %s" (term_to_string x) (term_to_string y))
              pairs))
            (match tac_opt with | None -> "no tactic" | Some tac -> term_to_string tac),
            (match goal with
            | None -> ""
            | Some t -> sprintf " in %s" (term_to_string t))
        | REWRITE { t1; t2 } ->
          sprintf "rewrite %s as %s" (term_to_string t1) (term_to_string t2), ""
        | WILD -> "_", ""
        | SHOW_PROOF_STATE _ -> "show_proof_state", ""
      in
      sprintf "%s %s %s; %s" with_prefix ht p
        (st_term_to_string' level t)
    | Tm_PragmaWithOptions { options; body } ->
      sprintf "#set-options \"%s\" {\n%s\n%s}"
        options (st_term_to_string' (indent level) body) level
    | Tm_ForwardJumpLabel { lbl; body; post } ->
      sprintf "%s\n%s:\n  ensures %s"
        (st_term_to_string' (indent level) body)
        (T.unseal lbl.name)
        (comp_to_string post)
    | Tm_Goto { lbl; arg } ->
      sprintf "goto %s %s"
        (term_to_string lbl)
        (term_to_string arg)

and branches_to_string brs : T.Tac _ =
  match brs with
  | [] -> ""
  | b::bs -> branch_to_string b ^ branches_to_string bs

and branch_to_string br : T.Tac _ =
  let {pat; e; norw} = br in
  Printf.sprintf "{ %s%s -> %s }"
    (pattern_to_string pat)
    (if T.unseal norw then "(norw)" else "")
    (st_term_to_string' "" e)

and pattern_to_string (p:pattern) : T.Tac string = 
  match p with
  | Pat_Cons fv pats ->
    Printf.sprintf "(%s %s)"
      (String.concat "." fv.fv_name) 
      (String.concat " " (T.map (fun (p, _) -> pattern_to_string p) pats))
  | Pat_Constant c ->
    "<constant>"
  | Pat_Var x _ ->
    T.unseal x
  | Pat_Dot_Term None ->
    ""
  | Pat_Dot_Term (Some t) ->
    Printf.sprintf "(.??)" //%s)" (term_to_string t)
    


let st_term_to_string t = st_term_to_string' "" t

let tag_of_term (t:term) =
  match inspect_term t with
  | Tm_Emp -> "Tm_Emp"
  | Tm_IsUnreachable -> "Tm_IsUnreachable"
  | Tm_Pure _ -> "Tm_Pure"
  | Tm_Star _ _ -> "Tm_Star"
  | Tm_ExistsSL _ _ _ -> "Tm_ExistsSL"
  | Tm_ForallSL _ _ _ -> "Tm_ForallSL"
  | Tm_WithPure .. -> "Tm_WithPure"
  | Tm_SLProp -> "Tm_SLProp"
  | Tm_Inames -> "Tm_Inames"
  | Tm_EmpInames -> "Tm_EmpInames"
  | Tm_Unknown -> "Tm_Unknown"
  | Tm_Inv _ _ -> "Tm_Inv"
  | Tm_FStar _ -> "Tm_FStar"

let tag_of_st_term (t:st_term) =
  match t.term with
  | Tm_Return _ -> "Tm_Return"
  | Tm_Abs _ -> "Tm_Abs"
  | Tm_ST _ -> "Tm_ST"
  | Tm_Bind _ -> "Tm_Bind"
  | Tm_TotBind _ -> "Tm_TotBind"
  | Tm_If _ -> "Tm_If"
  | Tm_Match _ -> "Tm_Match"
  | Tm_IntroPure _ -> "Tm_IntroPure"
  | Tm_ElimExists _ -> "Tm_ElimExists"
  | Tm_IntroExists _ -> "Tm_IntroExists"
  | Tm_NuWhile _ -> "Tm_NuWhile"
  | Tm_WithLocal _ -> "Tm_WithLocal"
  | Tm_WithLocalArray _ -> "Tm_WithLocalArray"
  | Tm_Rewrite _ -> "Tm_Rewrite"
  | Tm_Admit _ -> "Tm_Admit"
  | Tm_Unreachable _ -> "Tm_Unreachable"
  | Tm_ProofHintWithBinders _ -> "Tm_ProofHintWithBinders"
  | Tm_PragmaWithOptions _ -> "Tm_PragmaWithOptions"
  | Tm_ForwardJumpLabel _ -> "Tm_ForwardJumpLabel"
  | Tm_Goto _ -> "Tm_Goto"

let tag_of_comp (c:comp) : T.Tac string =
  match c with
  | C_Tot _ -> "Total"
  | C_ST _ -> "ST"
  | C_STAtomic i obs _ ->
    Printf.sprintf "%s %s" (observability_to_string obs) (term_to_string i)
  | C_STGhost _ _ ->
    "Ghost" 
    
let rec print_st_head (t:st_term)
  : Tot string (decreases t) =
  match t.term with
  | Tm_Abs _  -> "Abs"
  | Tm_Return p -> print_head p.term
  | Tm_Bind _ -> "Bind"
  | Tm_TotBind _ -> "TotBind"
  | Tm_If _ -> "If"
  | Tm_Match _ -> "Match"
  | Tm_NuWhile _ -> "NuWhile"
  | Tm_Admit _ -> "Admit"
  | Tm_Unreachable _ -> "Unreachable"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_WithLocalArray _ -> "WithLocalArray"
  | Tm_ST { t = p } -> print_head p
  | Tm_IntroPure _ -> "IntroPure"
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"  
  | Tm_ProofHintWithBinders _ -> "AssertWithBinders"
  | Tm_PragmaWithOptions _ -> "PragmaWithOptions"
  | Tm_ForwardJumpLabel _ -> "ForwardJumpLabel"
  | Tm_Goto _ -> "Goto"

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
  | Tm_NuWhile _ -> "NuWhile"
  | Tm_Admit _ -> "Admit"
  | Tm_Unreachable _ -> "Unreachable"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_WithLocalArray _ -> "WithLocalArray"
  | Tm_ST { t = p } -> print_head p
  | Tm_IntroPure _ -> "IntroPure"
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"
  | Tm_ProofHintWithBinders _ -> "AssertWithBinders"
  | Tm_PragmaWithOptions _ -> "PragmaWithOptions"
  | Tm_ForwardJumpLabel {body} -> Printf.sprintf "(ForwardJumpLabel %s)" (print_skel body)
  | Tm_Goto _ -> "Goto"

let decl_to_string (d:decl) : T.Tac string =
  match d.d with
  | FnDefn {id; isrec; bs; body} ->
    "fn " ^ (if isrec then "rec " else "") ^
     fst (R.inspect_ident id) ^ " " ^ 
     String.concat " " (T.map (fun (_, b, _) -> binder_to_string b) bs) ^
      " { " ^ st_term_to_string body ^ "}"
  | FnDecl {id; bs} ->
    "fn " ^
    fst (R.inspect_ident id) ^ " " ^
    String.concat " " (T.map (fun (_, b, _) -> binder_to_string b) bs)
