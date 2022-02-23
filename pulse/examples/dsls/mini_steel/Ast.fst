module Ast

type ident = string

type lident = {
  module_name: list string;
  identifier: string;
}

type constant =
  | Unit
  | Bool of bool
  | Int of int

type var =
  | Bound     of int
  | Free      of ident
  | Qualified of lident

type term =
  | TVar      : v:var -> term
  | TConstant : c:constant -> term
  | TApp      : head:var -> args:list term -> term
  | TLet      : x:ident -> e1:term -> e2:term -> term
  | TStar     : term -> term -> term
  | TExistsSL : x:ident -> term -> term
  | TForallSL : x:ident -> term -> term
  | TTotArrow : formals:list (ident & term) -> result:term -> term
  | TSTArrow  : formals:list (ident & term) -> result:st_comp -> term

and st_comp = {
  res: var;
  typ: term;
  pre: term;
  post: term
}

let typ = term

type atomic_stmt =
  | Expression : term -> atomic_stmt
  | App        : head:var -> args:list term -> atomic_stmt

type stmt =
  | Atomic        :  a:atomic_stmt -> stmt
  | LetBinding    : var:ident -> head:atomic_stmt -> body:stmt -> stmt
  // | LetMutBinding : var:ident -> head:atomic_stmt -> body:stmt -> stmt
  | Block         : stmt -> stmt
  | IfThenElse    : b:term ->
                    then_:stmt ->
                    else_:stmt ->
                    stmt

type decl =
  | Import    : name:ident -> modul:lident -> decl

  | Procedure : name:ident ->
                formals:list (ident & typ) ->
                result:st_comp ->
                body:stmt ->
                decl
