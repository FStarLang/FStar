%{
    open Pulse_Syntax

    let ctr : int ref = ref 0

    let get_next () : int =
      let r = !ctr in
      ctr := r + 1;
      r
    
    let names : ((string * int) list) ref =  ref []

    let begin_name_scope (s:string) =
      let c = get_next () in
      names := (s, c)::!names

    let lookup_name (s:string) : int option =
      let rec aux (l:(string * int) list) : int option =
        match l with
        | [] -> None
        | hd::tl -> if fst hd = s then Some (snd hd) else aux tl in
      aux !names

    let resolve_name (s:string) : term =
      match lookup_name s with
      | Some n -> Tm_Var {nm_ppname=s;nm_index=Z.of_int n}
      | None -> failwith ("Cannot resolve name " ^ s)

    let end_name_scope (s:string) (t:term) : term =
      match lookup_name s with
      | Some n -> close_term t (Z.of_int n)
      | None -> failwith ("end_name_scope, name not found " ^ s)

    let mk_app (head:term) (args:term list) : term =
      if List.length args = 0
      then Tm_STApp (head, Tm_Constant Unit)
      else
        let rec aux (acc:term) (args:term list) : term =
          match args with
          | [arg] -> Tm_STApp (acc, arg)
          | arg::args -> aux (Tm_PureApp (acc, arg)) args in
        aux head args

    let mk_fvar (l:string list) : term = Tm_FVar l

    let unsnoc (l:'a list) : ('a list * 'a) =
      let l = List.rev l in
      List.rev (List.tl l), List.hd l
    
    let mk_abs (bs:binder list) (pre:term) (body:term) : term =
      let bs, b = unsnoc bs in
      let t = Tm_Abs
                (b,
                 end_name_scope b.binder_ppname pre,
                 end_name_scope b.binder_ppname body) in
      List.fold_right (fun b t ->
                        let t = end_name_scope b.binder_ppname t in
                        Tm_Abs (b, Tm_Emp, t)) bs t

    let mk_pure_app (l:term list) : term =
      if List.length l < 2
      then failwith "mk_pure_app: list length < 2"
      else List.fold_left (fun t e ->
        Tm_PureApp (t, e)) (List.hd l) (List.tl l)
%}

%token<string> IDENT

%token EOF

%token FUN
%token TRUE FALSE
%token LPAREN RPAREN COMMA DOT COLON RARROW LBRACE RBRACE

%token EMP STAR

%start <term option> prog

%left STAR

%%

constant:
  | TRUE   { Bool (true) }
  | FALSE  { Bool (false) }

stapp:
  | head=pure_expr LPAREN args=arguments RPAREN    { mk_app head args }

arguments:
  | es=separated_nonempty_list(COMMA, pure_expr)    { es }

path:
  | id1=IDENT DOT id2=IDENT { [id1; id2] }
  | id=IDENT DOT p=path { id::p }

binder:
  | LPAREN s=IDENT COLON t=expr RPAREN
    {
      begin_name_scope s;
      {binder_ty=t; binder_ppname=s}
    }

binders:
  | bs=list(binder)    { bs }

lambda:
  | FUN b=binder RARROW e=expr
    {
      let e = end_name_scope b.binder_ppname e in
      Tm_Abs (b, Tm_Emp, e)
    }

  | FUN bs=binders LBRACE pre=pure_expr RBRACE RARROW e=expr
    {
      mk_abs bs pre e
    }

pureapp:
  | e1=pure_atomic_expr e2=pure_atomic_expr es=list(pure_atomic_expr)    { mk_pure_app (e1::e2::es) }

expr:
  | e=pure_expr             { e }
  | f=lambda                { f }
  | sapp=stapp              { sapp }
  | LPAREN e=expr RPAREN    { e }

pure_atomic_expr:
  | c=constant              { Tm_Constant (c) }
  | l=path                  { mk_fvar l }
  | i=IDENT                 { resolve_name i }
  | EMP                     { Tm_Emp }

pure_expr:
  | e=pure_atomic_expr    { e }
  | e=pureapp             { e }
  | e1=pure_expr STAR e2=pure_expr    { Tm_Star (e1, e2) }
  | LPAREN e=pure_expr RPAREN    { e }

prog:
  | EOF         { None }
  | e=expr EOF  { Some e }
;
