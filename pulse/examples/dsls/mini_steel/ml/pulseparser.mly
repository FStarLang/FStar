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
  | head=expr LPAREN args=arguments RPAREN    { mk_app head args }

right_flexible_list(SEP, X):
  |     { [] }
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

arguments:
  | es=right_flexible_list(COMMA, expr)    { es }

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
  | b=binder               { [b] }
  | b=binder bs=binders    {b::bs}

lambda:
  | FUN b=binder LBRACE pre=expr RBRACE RARROW LPAREN e=expr RPAREN
    {
      let pre = end_name_scope b.binder_ppname pre in
      let e = end_name_scope b.binder_ppname e in
      Tm_Abs (b, pre, e)
    }

  | FUN b=binder RARROW LPAREN e=expr RPAREN
    {
      let e = end_name_scope b.binder_ppname e in
      Tm_Abs (b, Tm_Emp, e)
    }

  | FUN bs=binders LBRACE pre=expr RBRACE RARROW LPAREN e=expr RPAREN
    {
      mk_abs bs pre e
    }

pureapp:
  | LPAREN e1=expr e2=expr RPAREN    { Tm_PureApp (e1, e2) }

expr:
  | c=constant              { Tm_Constant (c) }
  | l=path                  { mk_fvar l }
  | i=IDENT                 { resolve_name i }
  | f=lambda                { f }
  | papp=pureapp            { papp }
  | sapp=stapp              { sapp }
  | EMP                     { Tm_Emp }
  | e1=expr STAR e2=expr    { Tm_Star (e1, e2) }
  | LPAREN e=expr RPAREN    { e }

prog:
  | EOF         { None }
  | e=expr EOF  { Some e }
;
