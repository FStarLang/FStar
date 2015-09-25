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
let print_tag = false
let print_typ = false
let print_let_bindings = false
let print_ascribed = false

(* which kind of projection do we have? *)
type project =
  | LeftPro  
  | RightPro 
  | NoPro 

(* Function to inline expressions *)
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
    (* Something here makes the ocaml-binary segfault... *)
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
  | _ -> raise (Error("iNLINE can only be applied to variables", e.pos))


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
        (* R is always applied to 4 args: 2 types, 2 exp *)
        if List.length (args) <> 4 then 
          failwith "List does not have 4 arguments"
        else
          (* We replace the constructor application by one of it's arguments *)
          let arg0 = 
            if p = LeftPro then 
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
(*
  Util.print_string (typ_to_string (Util.compress_typ ty));
  Util.print_string "\n";
  Util.print_string (tag_of_typ  (Util.compress_typ ty) );
  Util.print_string "\n";
*)
  match (Util.compress_typ ty).n with
  (* If the type is "rel" or "double" it is "relational" *)
  | Typ_const f -> 
    f.v.ident.idText = "rel"  || 
    f.v.ident.idText = "double" ||
    f.v.ident.idText = "shared"  (* TODO: this is ad-hoc, maybe inline types? *)
  (* An application is relational if the head is relational *) (* TODO *)
  | Typ_app (head, args) -> 
    is_relational_typ head || false
    (*
    List.fold_left (fun b a -> b || (if is_inr (fst a) then
                                    begin
                                    (* TODO *)
                                      false
                                    end
                                    else
                                      is_relational_typ (left (fst a)))) false args
    *)
  (* A lambda is relational if its body is relational *)
  | Typ_lam (binders, body) -> is_relational_typ body

  | Typ_btvar b -> false (* TODO? *)

  (* A lambda is relational if its body is relational *)
  | Typ_fun (binders, comp) -> 
  begin
    match comp.n with
    | Total t -> is_relational_typ t
    | Comp ct -> is_relational_typ (ct.result_typ)
  end
    

  (* Placeholder for unimplemented cases *)
  | _ -> true (* TODO *)
       

(* Projection of types *)
let rec project_type (m:modul) (g:env) (ty:typ) (p:project) : typ =
(*
  Util.print_string "ProjectTyp\n";
  Util.print_string (typ_to_string (Util.compress_typ ty));
  Util.print_string "\n";
  Util.print_string (tag_of_typ  (Util.compress_typ ty) );
  Util.print_string "\n";
*)
  if p = NoPro then 
    ty
  else
  begin
    match (Util.compress_typ ty).n with
    (* Type applications *)
    | Typ_app (head, args) -> 
    begin  
      match head.n with 
      | Typ_const f -> 
        (* If the applied type is "rel" replace the type with the corresponding
           argument *) 
        begin
        match f.v.ident.idText with
        | "rel" ->
          begin
          match p with
(*
          | LeftPro -> project_type m g (left(fst(List.nth args 1))) p
          | RightPro -> project_type m g (left(fst(List.nth args 0))) p
*)
          | LeftPro -> left(fst(List.nth args 1))
          | RightPro -> left(fst(List.nth args 0))
          | NoPro -> failwith "Impossible"
          end

        | "double" -> left(fst(List.hd args))

        | _ -> 
        (* Otherwise we recursively project the arguments and re-assemble the
           Type-application *)
          let args' = (List.map (fun t -> if is_inr (fst t) then
                                                              Inr (project_p m g (right (fst t))  p), None 
                                                            else
                                                              Inl (project_type m g (left (fst t))  p), None) args) in 
          mk_Typ_app (head, args') (!(ty.tk)) (ty.pos)
        end
          
      | _ -> ty
    end

    (* Placeholder for unimplemented cases *)
    | _ -> ty
  end


(* Proejction of expressions  *)
and project_p (m:modul) (g:env) (e:exp) (p:project) : exp =
(*   let e = Tc.Normalize.norm_exp [Tc.Normalize.Beta;Tc.Normalize.SNComp;Tc.Normalize.Unmeta] g e in  *)
  if print_tag then
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
        (* new exp, new project, modified, continue recursively *)
        let e'', p', modf, cont = 
        match (Util.compress_exp head).n with
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
                  if p = LeftPro then 
                    List.nth args 2 
                  else  
                    List.nth args 3 in 
                right(fst arg0), p, true, false
            end
            else 
              e, p, false, true

          (* We want to replace applications of "compose2" with one of
             the arguments *)
          | "compose2"  -> 
            if p <> NoPro then
            begin
              (* compose2 is always applied to 11 args *)
              if List.length (args) <> 11 then 
                failwith "List does not have 11 arguments"
              else
                let arg0 = right(fst 
                  (if p = LeftPro then 
                    List.nth args 8 
                  else  
                    List.nth args 9)) in 
                let arg1 = project_p m  g (right(fst (List.nth args 10))) p  in 
                mk_Exp_app (arg0, [Inr arg1, None]) None e.pos, p, true, false
            end
            else
              e, p, false, true

          (* We want to inline code, so we can project it *)
          | "iNLINE" -> 
              if List.length (args) <> 2 then 
                failwith "List does not have 2 arguments"
              else
              begin
                let arg0 = List.nth args 1 in 
                let inline_e =  (right(fst arg0)) in 
                inline_exp g inline_e, p, true, true
              end

          (* When we find the projection keyword we set the projection in
             further recursive calls *)
          | "l_PROJECT" -> 
            if p <> NoPro then 
              raise (Error ("Illegal nested projection!", e.pos))
            else
              if List.length (args) <> 3 then 
                failwith "List does not have 3 arguments"
              else
                let arg0 = List.nth args 2 in 
                right(fst arg0), LeftPro, true, true

          | "r_PROJECT" -> 
            if p <> NoPro then 
              raise (Error ("Illegal nested projection!", e.pos))
            else
              if List.length (args) <> 3 then 
                failwith "List does not have 3 arguments"
              else
                let arg0 = List.nth args 2 in 
                right(fst arg0), RightPro, true, true

          (* We have special projections for some special functions *)
          | "rel_map1"
          | "rel_map2"
          | "rel_map3"
          | "twice"
          | "compose2_self" 
          | "pair_rel"
          | "cons_rel"
          | "tl_rel"
          | "fst_rel"
          | "snd_rel"
          | "sel_rel" ->
            if p <> NoPro then
            begin
              let head' = inline_exp g head in
              mk_Exp_app (head',args) None e.pos, p, true, true
            end
            else
              e, p, false, true
          | _ ->  e, p, false, true
        end
       | _ -> e, p, false, true in 

       if not (cont) then 
         e''
       else
       begin
         if not modf then 
         begin
           match (Util.compress_exp e'').n with
           | Exp_app (head, args) -> 
              let head' = project_p m g head p' in
              let args' = List.map (fun (a,q) -> if is_inr a then (Inr (project_p m g (right a) p'),q) else (a, q)) args in 
              mk_Exp_app (head', args') None e.pos
           | _ -> failwith "IMPOSSIBLE!"
         end
         else 
           project_p m g e'' p'
        end
      end
    (* We recursively project the body of abstractions *)
    | Exp_abs(binders, e') -> let e'' = project_p m g e' p in 
                              (* TODO *)
                              mk_Exp_abs (binders, e'') (!(e.tk)) e.pos

    (* We recursively project ascribed expressions *)
    | Exp_ascribed(e', t, eff) -> if print_ascribed then
                                  begin
                                    Util.print_string (exp_to_string e);
                                    Util.print_string "\n"
                                  end
                                  else () ;
                                  let e'' = project_p m g e' p in 
                                  let t' = project_type m g t p in
                                  let e = mk_Exp_ascribed (e'', t',  eff) (!(e.tk)) e.pos in 

                                  if print_ascribed then
                                  begin
                                    Util.print_string (exp_to_string e);
                                    Util.print_string "\n"
                                  end
                                  else () ;

                                  e
    | Exp_fvar (f, _) ->  let t = f.sort in 
(*
                          Util.print_string "\nReached variable: ";
                          Util.print_string (exp_to_string e);
                          Util.print_string "\n";
*)
                          if is_relational_typ t && p <> NoPro then 
                            let ident = {idText = f.v.ident.idText ^ (if p = LeftPro then "_l" else "_r") ;
                                         idRange = f.v.ident.idRange;} in
                            let lident = {ns = [];
                                          ident = ident;
                                          nsstr = m.name.str;
                                          str = (m.name.str ^ "." ^ ident.idText);} in 
                            let new_v = {v = lident;
                                         sort = mk_Typ_unknown ; (* TODO? *)
                                         p = e.pos} in
                            mk_Exp_fvar (new_v, None) None e.pos
                          else
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
                                                  if is_relational_typ lb.lbtyp || (p = NoPro) then
                                                    project_p m g (lb.lbdef) p  (* TODO project type? *)
                                                  else
                                                  begin
(*                                                     Util.print_string "dropped let!\n"; *)
                                                    mk_Exp_constant Const_unit None (lb.lbdef.pos) 
                                                  end in
                                                {lb with lbdef = lb_new}) (snd lbs) in

                           let e'' = project_p m g e' p in

                           mk_Exp_let (lbs' , e'') (!(e.tk)) e.pos 
    (* We recursively project matches *)
    | Exp_match(e', pats) -> let e'' = project_p m g e' p in
                             (* We also project patterns *)
                             let pats' = List.map  (fun (pat, t, pe) -> 
                                                   (project_pat pat p,
                                                    t,
                                                    project_p m g pe p))pats in
                             mk_Exp_match (e'', pats') (!(e.tk)) e.pos

    | Exp_meta(Meta_desugared(e, _)) -> project_p m g e p
                                          
    (* Placeholder for unimplemented caese *)
    | Exp_bvar bvv -> 
(*
                      Util.print_string "Bvar : ";
                      Util.print_string (exp_to_string e );
                      Util.print_string "\n\n";
*)
                      e
    | _ -> e in 

(*   Util.print_string "returning...\n"; *)

  if print_post && p <> NoPro then 
  begin
    Util.print_string (exp_to_string  e') ;
    Util.print_string "\n \n" 
  end;

  e'


(* Function to project expressions: *)
let project_exp (m:modul) (g:env) (e:exp) : exp =
  let r = project_p m g e NoPro in 
  let r = Tc.Normalize.norm_exp [Tc.Normalize.Beta;Tc.Normalize.SNComp;Tc.Normalize.Unmeta] g r in 
  r
