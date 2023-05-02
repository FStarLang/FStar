module PulseSugar
open FStar.Ident
module A = FStar.Parser.AST
let rng = FStar.Compiler.Range.range

type binder = A.aqual & ident & A.term

type binders = list binder

type vprop =
  | VPropTerm of A.term
  | VPropExists {
      binders:binders;
      body:vprop
    }

type st_comp_tag = 
  | ST
  | STAtomic of A.term
  | STGhost of A.term

type computation_type = {
     tag: st_comp_tag;
     precondition:vprop;
     return_name:ident;
     return_type:A.term;
     postcondition: vprop;
     range:rng
}

type mut_or_ref =
  | MUT | REF

type pat = 
  | PatVar of ident
  | PatConstructor {
      head:lident;
      args:list pat
    }
    
type stmt' =
  | Expr { 
      e : A.term 
    }

  | Assignment {
      id:ident;
      value:A.term;
    }

  | LetBinding {
      qualifier: option mut_or_ref;
      id:ident;
      typ:option A.term;
      init:option A.term;
    }
      
  | Block { 
      stmt : stmt
    }
    
  | If {
      head:A.term;
      join_vprop:option vprop;
      then_:stmt;
      else_opt:option stmt;
    }

  | Match {
      head:A.term;
      returns_annot:option computation_type;
      branches:list (A.pattern & stmt);
    }

  | While {
      head: A.term;
      id: ident;
      invariant: vprop;
      body: stmt;
    }

  | Sequence {
      s1:stmt;
      s2:stmt;
    }

and stmt = {
  s:stmt';
  range:rng
}

type decl = {
  id:ident;
  binders:binders;
  ascription:computation_type;
  body:stmt;
  range:rng
}


(* Convenience builders for use from OCaml/Menhir, since field names get mangled in OCaml *)
let mk_comp tag precondition return_name return_type postcondition range = 
  {
     tag;
     precondition;
     return_name;
     return_type;
     postcondition;
     range
  }

let mk_vprop_exists binders body = VPropExists { binders; body }
let mk_expr e = Expr { e }
let mk_assignment id value = Assignment { id; value }
let mk_let_binding qualifier id typ init = LetBinding { qualifier; id; typ; init }
let mk_block stmt = Block { stmt }
let mk_if head join_vprop then_ else_opt = If { head; join_vprop; then_; else_opt }
let mk_match head returns_annot branches = Match { head; returns_annot; branches }
let mk_while head id invariant body = While { head; id; invariant; body }
let mk_sequence s1 s2 = Sequence { s1; s2 }
let mk_stmt s range = { s; range }
let mk_decl id binders ascription body range = { id; binders; ascription; body; range }
