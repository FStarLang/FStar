#light "off"
module FStar.Projection.ProjectExp
open FStar
open FStar.Util
open FStar.Projection.Util
open FStar.Absyn
open FStar.Tc.Env
open FStar.Absyn.Syntax
open FStar.Absyn.Print

(* Debug Output *)
let print_pre = false
let print_post = false
let print_tag = true
let print_typ = false
let print_let_bindings = true
let print_ascribed = false
let print_expression_projection = false
let print_pattern_projection = false

(* which kind of projection do we have? *)
type project =
  | Left  
  | Right 
  | NoPro 

let inline_exp (g:env) (e:exp) : exp =
  match (Util.compress_exp e).n with
  (* The inlined expression should be a variable *)
  | Exp_fvar (f, _) -> 
    let id = exp_to_string e in 
    let nsstr = f.v.nsstr in
    let mods = g.modules in 
    (* Look for a module with the correct name *)
    let modl = Option.get (list_find 
      (fun m -> m.name.str = nsstr) mods) in 
    let decs = modl.declarations in 
    (* Look for a declaration declaring this expressions *)
    let dec = Option.get (list_find 
      (fun d -> match d with 
        | Sig_let (lbs, _, _, _) ->
          list_exists (fun lb -> lbname_to_string (lb.lbname) = id) (snd lbs)
        | _ -> false) 
      decs) in 
    let lbs = match dec with 
              | Sig_let (lbs', _, _, _) -> lbs' 
              | _ -> failwith "Impossible!" in 
    (* Look for the letbinding defining this expression *)
    let lb = Option.get (list_find (fun lb -> lbname_to_string lb.lbname = id) (snd lbs)) in
    (* apply projecction to this expression and return the
       result *)
    lb.lbdef


(* Projection of patterns *)
let rec project_pat (pa:pat) (p:project) : pat =
  if p = NoPro then
    pa 
  else
  begin
    match pa.v with 
    (* Constructor application *)
    | Pat_cons (f, q , args) -> 
      (* We check if the constructor is "R" and we are in a projection mode *)
      if f.v.ident.idText = "R" && p <> NoPro then 
      begin 
        if print_pattern_projection then 
          Util.print_string "Pattern Projection \n\n";

        (* R is always applied to 4 args: 2 types, 2 exp *)
        if List.length (args) <> 4 then 
          failwith "List does not have 4 arguments"
        else
          (* We replace the constructor application by one of it's arguments *)
          let arg0 = 
            if p = Left then 
              List.nth args 2 
            else  
              List.nth args 3 in 
          (fst arg0)
      end
      else 
      (* Otherwise We recurively apply the projection to the argument list 
         (Only to arguments that are not explicit implicits *)
      begin
        let args' = List.map (fun a -> if snd a then 
                                         a
                                       else
                                         (project_pat (fst a) p), snd a) args in 
          
        (* We re-assemble the contructor application *)
        let pa' = Pat_cons (f, q, args')
        in {pa with v = pa'}
      end

    (* Placeholder for unimplemented cases *)
    | _ -> pa
  end

(* Check if a type is relational *)
let rec is_relational_typ (ty:typ) : bool = 
  match (Util.compress_typ ty).n with
  (* If the type is "rel" or "double" it is "relational" *)
  | Typ_const f -> 
    f.v.ident.idText = "rel"  || 
    f.v.ident.idText = "double" 
  (* An application is relational if the head is relational *) (* TODO *)
  | Typ_app (head, args) -> 
    is_relational_typ head || 
    List.fold_left (fun b a -> b || (if is_inr (fst a) then
                                    begin
                                    (* TODO *)
                                      false
                                    end
                                    else
                                      is_relational_typ (left (fst a)))) false args
  (* A lambda is relational if its body is relational *)
  | Typ_lam (binders, body) -> is_relational_typ body

  (* Placeholder for unimplemented cases *)
  | _ -> true (* TODO *)
       

(* Projection of types *)
let rec project_typ (ty:typ) (p:project) : typ =
  if p = NoPro then 
    ty
  else
    match (Util.compress_typ ty).n with
    (* Type applications *)
    | Typ_app (head, args) -> 
    begin  
      match head.n with 
      | Typ_const f -> 
        (* If the applied type is "rel" replace the type with the corresponding
           argument *) 
        match f.v.ident.idText with
        | "rel" ->
          begin
          match p with
(*
          | Left -> project_typ (left(fst(List.nth args 1))) p
          | Right -> project_typ (left(fst(List.nth args 0))) p
*)
          | Left -> left(fst(List.nth args 1))
          | Right -> left(fst(List.nth args 0))
          | NoPro -> failwith "Impossible"
          end

        | "double" -> left(fst(List.hd args))

        | _ -> 
        (* Otherwise we recursively project the arguments and re-assemble the
           Type-application *)
          let args' = (List.map (fun t -> Inl (project_typ (left (fst t))  p), None) args) in 
          mk_Typ_app (head, args') (!(ty.tk)) (ty.pos)
          
      | _ -> ty
    end

    (* Placeholder for unimplemented cases *)
    | _ -> ty



(* Proejction of expressions  *)
let rec project_p (g:env) (e:exp) (p:project) : exp =
  let e = Tc.Normalize.norm_exp [Tc.Normalize.Beta;Tc.Normalize.SNComp;Tc.Normalize.Unmeta] g e in 
  if print_tag && p <> NoPro then
  begin
    Util.print_string (tag_of_exp e);
    Util.print_string "\n"
  end;


  if print_pre && p <> NoPro then 
  begin
    Util.print_string (exp_to_string  e) ;
    Util.print_string "\n\n"
  end;

  if print_pre (* && p <> NoPro*) then 
  begin
    let t = (!((Util.compress_exp e).tk)) in 
    if is_some t then 
    begin
      let t' = Option.get t in 
      Util.print_string (typ_to_string  t');
      Util.print_string "\n"
    end
  end;

  (* Recursively go through the expression *)
  let e' = match (Util.compress_exp e).n with
    | Exp_app (head, args) -> 
      let head = Util.compress_exp head in
      begin 
        let e'', p' = 
        match head.n with
        | Exp_fvar (f, _)  -> 
          begin
            match f.v.ident.idText with
            (* We want to replace applications of "R" with one of the
               arguments *)
            | "R"  -> 
              if p <> NoPro then
              begin
                (* R is always applied to 4 args: 2 types, 2 exp *)
                if List.length (args) <> 4 then 
                  failwith "List does not have 4 arguments"
                else
                  let arg0 = 
                    if p = Left then 
                      List.nth args 2 
                    else  
                      List.nth args 3 in 
                  right(fst arg0)
              end
              else 
                e'

            (* We want to replace applications of "twice" with its argument
                *)
            | "twice"  -> 
              if p <> NoPro then
              begin
                if print_expression_projection then 
                  Util.print_string "Expression Projection \n\n" 
                else ();

                (* R is always applied to 2 args: 1 types, 1 exp *)
                if List.length (args) <> 2 then 
                  failwith "List does not have 2 arguments"
                else
                  let arg0 = List.nth args 1 in 
                  right(fst arg0)
              end
              else 
                e'

            (* We want to replace applications of "compose2" with one of
               the arguments *)
            | "compose2"  -> 
              if p <> NoPro then
              begin
                if print_expression_projection then 
                  Util.print_string "Expression Projection \n\n" 
                else ();

                (* compose2 is always applied to 11 args *)
                if List.length (args) <> 11 then 
                  failwith "List does not have 11 arguments"
                else
                  let arg0 = right(fst 
                    (if p = Left then 
                      List.nth args 8 
                    else  
                      List.nth args 9)) in 
                  let arg1 = right(fst (List.nth args 10)) in 
                  mk_Exp_app (arg0, [Inr arg1, None]) None e.pos
              end
              else
                e'

            (* We want to replace applications of "compose2_self" with its
               arguments *)
            | "compose2_self"  -> 
              if p <> NoPro then
              begin
                if print_expression_projection then 
                  Util.print_string "Expression Projection \n\n" 
                else ();

                (* compose2_self is always applied to 6 args *)
                if List.length (args) <> 6 then 
                  failwith "List does not have 6 arguments"
                else
                  let arg0 = right(fst (List.nth args 4)) in 
                  let arg1 = right(fst (List.nth args 5)))in 
                  mk_Exp_app (arg0, [Inr arg1, None]) None e.pos
              end
              else 
                e'

            (* We want to inline code, so we can project it *)
            | "iNLINE" -> 
                if List.length (args) <> 2 then 
                  failwith "List does not have 2 arguments"
                else
                begin
                  let arg0 = List.nth args 1 in 
                  let inline_e =  (right(fst arg0)) in 
                  inline_exp g inline_e
                end

            (* When we find the projection keyword we set the projection in
               further recursive calls *)
            | "l_PROJECT" -> 
              if p <> NoPro then 
                failwith "Illegal nested projection!"
              else
                if List.length (args) <> 3 then 
                  failwith "List does not have 3 arguments"
                else
                  let arg0 = List.nth args 2 in 
                  (* TODO really go recursive here? *)
                  roject_p g (right(fst arg0)) Left

            | "r_PROJECT" -> 
              if p <> NoPro then 
                failwith "Illegal nested projection!"
              else
                if List.length (args) <> 3 then 
                  failwith "List does not have 3 arguments"
                else
                  let arg0 = List.nth args 2 in 
                  project_p g (right(fst arg0)) Right

            (* We have special projections for some special functions *)
            | "rel_map1" -> 
            | "rel_map2" -> 
            | "rel_map3" -> 
              if p <> NoPro then
              begin
                let head' = inline_exp head in
                mk_Exp_app (head',args) None e.pos
              end
              else
                e
            | _ -> 
              let head' = project_p g head p in
              let args' = List.map (fun (a,q) -> if is_inr a then (Inr (project_p g (right a) p),q) else (a, q)) args in 
              mk_Exp_app (head', args') None e.pos
          end
//           | Exp_fvar (f, _)  -> if true then begin Util.print_string f.v.ident.idText; Util.print_string "\n\n" ;e end 
//                                                             else e
       | _ -> 
          let head' = project_p g head p in
          let args' = List.map (fun (a,q) -> if is_inr a then (Inr (project_p g (right a) p),q) else (a, q)) args in 
          mk_Exp_app (head', args') None e.pos

      end
    (* We recursively project the body of abstractions *)
    | Exp_abs(binders, e') -> let e'' = project_p g e' p in 
                              (* TODO *)
                              mk_Exp_abs (binders, e'') (!(e.tk)) e.pos

    (* We recursively project ascribed expressions *)
    | Exp_ascribed(e', t, eff) -> if print_ascribed then
                                  begin
                                    Util.print_string (exp_to_string e);
                                    Util.print_string "\n"
                                  end
                                  else () ;
                                  let e'' = project_p g e' p in 
                                  let t' = project_typ t p in
                                  let e = mk_Exp_ascribed (e'', t',  eff) (!(e.tk)) e.pos in 

                                  if print_ascribed then
                                  begin
                                    Util.print_string (exp_to_string e);
                                    Util.print_string "\n"
                                  end
                                  else () ;

                                  e
    | Exp_fvar (f, _) -> let t = f.sort in 
                         Util.print_string (Util.format2 "%s: %s\n" (f.v.ident.idText) (typ_to_string t));
                         e

                            
    (* We recursively project let-expressions *)
    | Exp_let (lbs, e') -> (* Project the continuation *)
                           if print_let_bindings then 
                           begin
                             Util.print_string "\n";
                             Util.print_string "Found let expression: ";
                             Util.print_string (lbname_to_string ((List.hd (snd lbs)).lbname)) ;
                             Util.print_string "\n"
                           end
                           else ();

                           (* project on all bindings *)
                           let lbs' = fst lbs,  List.map (fun lb ->  
                                                let lb_new =
                                                  if is_relational_typ lb.lbtyp then
                                                    project_p g (lb.lbdef) p  (* TODO project type? *)
                                                  else
                                                    mk_Exp_constant Const_unit None (lb.lbdef.pos) in 
                                                {lb with lbdef = lb_new}) (snd lbs) in

                           let e'' = project_p g e' p in

                           mk_Exp_let (lbs' , e'') (!(e.tk)) e.pos 
    (* We recursively project matches *)
    | Exp_match(e', pats) -> let e'' = project_p g e' p in
                             (* We also project patterns *)
                             let pats' = List.map  (fun (pat, t, pe) -> 
                                                   (project_pat pat p,
                                                    t,
                                                    project_p g pe p))pats in
                             mk_Exp_match (e'', pats') (!(e.tk)) e.pos

    | Exp_meta(Meta_desugared(e, _)) -> project_p g e p
                                          
    (* Placeholder for unimplemented caese *)
    | _ -> e in 

  if print_post && p <> NoPro then 
  begin
    Util.print_string (exp_to_string  e') ;
    Util.print_string "\n \n" 
  end
  else () ;

  e'

let project_exp (g:env) (e:exp) : exp =
  let r = project_p g e NoPro in 
  r

(*
and exp_to_string x = match (compress_exp x).n with
  | Exp_delayed _ -> failwith "Impossible"
  | Exp_meta(Meta_desugared(e, _)) -> exp_to_string e
  | Exp_uvar(uv, t) -> uvar_e_to_string (uv, t)
  | Exp_bvar bvv -> strBvd bvv.v //Util.format2 "%s : %s" (strBvd bvv.v) (typ_to_string bvv.sort)
  | Exp_fvar(fv, _) ->  sli fv.v
  | Exp_constant c -> c |> const_to_string
  | Exp_abs(binders, e) -> Util.format2 "(fun %s -> %s)" (binders_to_string " " binders) (e|> exp_to_string)
  | Exp_app(e, args) ->
      let lex = if !Options.print_implicits then None else reconstruct_lex x in
      (match lex with
      | Some es -> "%[" ^ (String.concat "; " (List.map exp_to_string es)) ^ "]"
      | None ->
          let args' = filter_imp args |> List.filter (function (Inr _, _) -> true | _ -> false) in
            (* drop implicit and type arguments for prim operators (e.g equality) *)
            (* we drop the type arguments because they should all be implicits,
               but somehow the type-checker/elaborator doesn't always mark them as such
               (TODO: should file this as a bug) *)
          if is_infix_prim_op e && List.length args' = 2 then
            Util.format3 "(%s %s %s)" (List.nth args' 0 |> arg_to_string) (e|> infix_prim_op_to_string) (List.nth args' 1 |> arg_to_string)
          else if is_unary_prim_op e && List.length args' = 1 then
            Util.format2 "(%s %s)" (e|> unary_prim_op_to_string) (List.nth args' 0 |> arg_to_string)
          else Util.format2 "(%s %s)" (e|> exp_to_string) (args_to_string args))
  | Exp_match(e, pats) -> Util.format2 "(match %s with %s)"
    (e |> exp_to_string)
    (Util.concat_l "\n\t" (pats |> List.map (fun (p,wopt,e) -> Util.format3 "%s %s -> %s"
      (p |> pat_to_string)
      (match wopt with | None -> "" | Some w -> Util.format1 "when %s" (w |> exp_to_string))
      (e |> exp_to_string))))
  | Exp_ascribed(e, t, _) -> Util.format2 "(%s:%s)" (e|> exp_to_string) (t |> typ_to_string)
  | Exp_let(lbs, e) -> Util.format2 "%s in %s"
    (lbs_to_string lbs)
    (e|> exp_to_string)
    *)
