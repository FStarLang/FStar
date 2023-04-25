%{
    open Pulse_Syntax
    open Pulse_Util
    
    let ctr : int ref = ref 0

    let get_next () : int =
      let r = !ctr in
      ctr := r + 1;
      r

    (* the boolean is false when the name is
       introduced from a let
       since the ast does not yet have binder on Tm_Bind,
       we need to turn the ppname of let name uses into _
    
       see resolve_name later *)
    let names : ((string * int * bool) list) ref =  ref []

    let begin_name_scope (s:string) =
      let c = get_next () in
      names := (s, c, true)::!names

    let begin_null_name_scope (s:string) =
      let c = get_next () in
      names := (s, c, false)::!names

    let lookup_name (s:string) : (int * bool) option =
      let rec aux (l:(string * int * bool) list) : (int * bool) option =
        match l with
        | [] -> None
        | (s', i, b)::tl -> if s' = s then Some (i, b) else aux tl in
      aux !names

    let resolve_name (s:string) : term =
      match lookup_name s with
      | Some (n, b) ->
        Tm_Var { nm_ppname=if b then s else "_";
                 nm_index=Z.of_int n;
                 nm_range=FStar_Range.range_0}
      | None -> raise (Syntax_error ("Cannot resolve name " ^ s))

    let lookup_var_index (s:string) : Z.t =
          match lookup_name s with
      | Some (n, _) -> Z.of_int n
      | None -> raise (Syntax_error("lookup_var_index, name not found " ^ s))

    let mk_app (head:term) (args:(qualifier option * term) list) : st_term =
      if List.length args = 0
      then Tm_STApp (head, None, Tm_Constant Unit)
      else
        let rec aux (acc:term) (args:(qualifier option * term) list) : st_term =
          match args with
          | [q, arg] -> Tm_STApp (acc, q, arg)
          | (q, arg)::args -> aux (Tm_PureApp (acc, q, arg)) args in
        aux head args

    let mk_st_app (app:term) =
        match app with
        | Tm_PureApp(head, q, arg) -> Tm_STApp(head, q, arg)
        | _ -> Tm_Return (STT, false, app)
        
    let mk_fvar (l:string list) (us:universe list)
        : term
        = match us with
          | [] -> Tm_FVar (Pulse_Syntax.as_fv l)
          | _ -> Tm_UInst (Pulse_Syntax.as_fv l, us)

    let unsnoc (l:'a list) : ('a list * 'a) =
      let l = List.rev l in
      List.rev (List.tl l), List.hd l
    
    let mk_abs (bs:(qualifier option * binder) list) (pre:term) (body:st_term) (post_opt:term option) : st_term =
      let bs, (q, b) = unsnoc bs in
      let b_index = lookup_var_index b.binder_ppname in
      let t = Tm_Abs
                (b,
                 q,
                 (Some (close_term pre b_index)),
                 close_st_term body b_index,
                 (match post_opt with
                  | None -> None
                  | Some post ->
                    Some (close_term' post b_index (Z.of_int 1)))) in
      List.fold_right (fun (q, b) t ->
                        let t = close_st_term t (lookup_var_index b.binder_ppname) in
                        Tm_Abs (b, q, Some Tm_Emp, t, None)) bs t

    let mk_pure_app (head:term) (l:(qualifier option * term) list) : term =
      match l with
      | [] -> raise (Syntax_error ("mk_pure_app: no arguments"))
      | _ ->
        List.fold_left
                (fun t (q, e) -> Tm_PureApp (t, q, e))
                head
                l
%}

%token<string> IDENT

%token EOF

%token FUN LET RETURN HASH_IMPLICIT U_HASH_ZERO REQUIRES ENSURES
%token TRUE FALSE
%token LPAREN RPAREN COMMA DOT COLON RARROW LBRACE RBRACE EQUALS SEMICOLON

%token EMP STAR

%start <st_term option> prog

%left STAR

%%

constant:
  | TRUE   { Bool (true) }
  | FALSE  { Bool (false) }

stapp:
  | head=pure_expr LBRACE args=arguments RBRACE    { mk_app head args }

arg:
  | q=option(qualifier) e=pure_expr
    { (q, e) }
    
arguments:
  | es=separated_nonempty_list(COMMA, arg)    { es }

path:
  | id1=IDENT DOT id2=IDENT { [id1; id2] }
  | id=IDENT DOT p=path { id::p }

binder:
  | LPAREN q=option(qualifier) s=IDENT COLON t=pure_expr RPAREN
    {
      begin_name_scope s;
      q, {binder_ty=t; binder_ppname=s}
    }

binder_noqual:
  | LPAREN s=IDENT COLON t=pure_expr RPAREN
    {
      begin_name_scope s;
      {binder_ty=t; binder_ppname=s}
    }

let_binder:
  | s=IDENT
    {
      begin_null_name_scope s;
      s
    }

null_name:
  | s=IDENT
    {
      begin_null_name_scope s;
      s
    }

lambda_post:
   | s=null_name DOT post=pure_expr
    {
      close_term post (lookup_var_index s)
    }

binders:
  | bs=list(binder)    { bs }

requires:
  | REQUIRES pre=pure_expr
    { pre }

ensures:
  | ENSURES post=lambda_post
    { post }

lambda:
  | FUN bs=binders pre=requires post=ensures RARROW e=expr
    {
      mk_abs bs pre e (Some post)
    }

qualifier:
  | HASH_IMPLICIT { Implicit }

qualified_arg:
  | q=option(qualifier) e=pure_atomic_expr
    { (q, e) }
  
pureapp:
  | e1=pure_atomic_expr e2=qualified_arg es=list(qualified_arg)    { mk_pure_app e1 (e2::es) }

expr:
  | RETURN e=pure_expr      { Tm_Return (STT, false, e) }
  | app=pureapp            { mk_st_app app }
  | LET b=let_binder EQUALS e1=pureapp SEMICOLON e2=expr
    {
      let e2 = close_st_term e2 (lookup_var_index b) in
      Tm_Bind (mk_st_app e1, e2)
    }
  | e1=pureapp SEMICOLON e2=expr    { Tm_Bind (mk_st_app e1, e2) }
(*  | LPAREN e=expr RPAREN    { e } *)


universe:
  | U_HASH_ZERO
    { U_zero } 
  
pure_atomic_expr:
  | c=constant              { Tm_Constant (c) }
  | l=path us=list(universe) { mk_fvar l us }
  | i=IDENT                 { resolve_name i }
  | EMP                     { Tm_Emp }
  | LPAREN e=pure_expr RPAREN  { e }
  
pure_expr:
  | e=pure_atomic_expr                    { e }
  | e=pureapp                             { e }
  | e1=pure_expr STAR e2=pure_expr        { Tm_Star (e1, e2) }
  | b=binder_noqual LBRACE e=pure_expr RBRACE
    {
      let e = close_term e (lookup_var_index b.binder_ppname) in
      Tm_Refine (b, e)
    }


prog:
  | EOF           { None }
  | e=lambda EOF  { Some e }
  | e=expr   EOF  { Some e }
;
