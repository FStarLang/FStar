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

module PulseSyntaxExtension.Sugar
open FStar.Ident
module A = FStar.Parser.AST
let rng = FStar.Compiler.Range.range
let dummyRange = FStar.Compiler.Range.dummyRange

//Note: We do not yet process binder attributes, like typeclass attributes
type binder = A.binder
type binders = list binder

type vprop' =
  | VPropTerm of A.term

and vprop = {
  v:vprop';
  vrange:rng
}

let as_vprop (v:vprop') (r:rng) = { v; vrange=r}

type st_comp_tag = 
  | ST
  | STAtomic
  | STGhost

type computation_type = {
     tag: st_comp_tag;
     precondition:vprop;
     return_name:ident;
     return_type:A.term;
     postcondition:vprop;
     opens:option A.term;
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

type hint_type =
  | ASSERT of vprop
  | UNFOLD of option (list lident) & vprop
  | FOLD of option (list lident) & vprop
  | RENAME of
      list (A.term & A.term) &
      option vprop & (* in goal *)
      option A.term (* optional tactic *)
  | REWRITE of
      vprop &
      vprop &
      option A.term (* optional tactic *)
  | WILD
  | SHOW_PROOF_STATE of rng

type array_init = {
  init : A.term;
  len : A.term;
}

let ensures_vprop = option (ident & A.term) & vprop & option A.term

type stmt' =
  | Open of lident
  
  | Expr { 
      e : A.term 
    }

  | Assignment {
      lhs:A.term;
      value:A.term;
    }

  | ArrayAssignment {
      arr:A.term;
      index:A.term;
      value:A.term;
    }

  | LetBinding {
      qualifier: option mut_or_ref;
      id:ident;
      typ:option A.term;
      init:option let_init
    }
      
  | Block { 
      stmt : stmt
    }
    
  | If {
      head:A.term;
      join_vprop:option ensures_vprop;
      then_:stmt;
      else_opt:option stmt;
    }

  | Match {
      head:A.term;
      returns_annot:option ensures_vprop;
      branches:list (A.pattern & stmt);
    }

  | While {
      guard: stmt;
      id: ident;
      invariant: vprop;
      body: stmt;
    }

  | Introduce {
      vprop:vprop;
      witnesses:list A.term
    }
      
  | Sequence {
      s1:stmt;
      s2:stmt;
    }

  | Parallel {
      p1:vprop;
      p2:vprop;
      q1:vprop;
      q2:vprop;
      b1:stmt;
      b2:stmt;
    }

  | ProofHintWithBinders {
      hint_type:hint_type;
      binders:binders;
    }

  | WithInvariants {
      names : list A.term;
      body  : stmt;
      returns_ : option ensures_vprop;
    }

and stmt = {
  s:stmt';
  range:rng
}

and lambda = {
  binders:binders;
  ascription:option computation_type;
  body:stmt;
  range:rng
}

and fn_defn = {
  id:ident;
  is_rec:bool;
  binders:binders;
  ascription:either computation_type (option A.term);
  measure:option A.term; // with binders in scope
  body:either stmt lambda;
  range:rng
}

and let_init =
  | Array_initializer of array_init
  | Default_initializer of A.term
  | Lambda_initializer of fn_defn
  | Stmt_initializer of stmt

type fn_decl = {
  id:ident;
  binders:binders;
  ascription:either computation_type (option A.term); (* always Inl for now *)
  range:rng
}

let tag_of_stmt (s:stmt) : string =
  match s.s with
  | Open _ -> "Open"
  | Expr {} -> "Expr"
  | Assignment {} -> "Assignment"
  | ArrayAssignment {} -> "ArrayAssignment"
  | LetBinding {} -> "LetBinding"
  | Block {} -> "Block"
  | If {} -> "If"
  | Match {} -> "Match"
  | While {} -> "While"
  | Introduce {} -> "Introduce"
  | Sequence {} -> "Sequence"
  | Parallel {} -> "Parallel"
  | ProofHintWithBinders {} -> "ProofHintWithBinders"
  | WithInvariants {} -> "WithInvariants"

type decl =
  | FnDefn of fn_defn
  | FnDecl of fn_decl
  
(* Convenience builders for use from OCaml/Menhir, since field names get mangled in OCaml *)
let mk_comp tag precondition return_name return_type postcondition opens range = 
  {
     tag;
     precondition;
     return_name;
     return_type;
     postcondition;
     opens;
     range
  }

// let mk_vprop_exists binders body = VPropExists { binders; body }
let mk_expr e = Expr { e }
let mk_assignment id value = Assignment { lhs=id; value }
let mk_array_assignment arr index value = ArrayAssignment { arr; index; value }
let mk_let_binding qualifier id typ init = LetBinding { qualifier; id; typ; init }
let mk_block stmt = Block { stmt }
let mk_if head join_vprop then_ else_opt = If { head; join_vprop; then_; else_opt }
let mk_match head returns_annot branches = Match { head; returns_annot; branches }
let mk_while guard id invariant body = While { guard; id; invariant; body }
let mk_intro vprop witnesses = Introduce { vprop; witnesses }
let mk_sequence s1 s2 = Sequence { s1; s2 }
let mk_stmt s range = { s; range }
let mk_fn_defn id is_rec binders ascription measure body range : fn_defn = { id; is_rec; binders; ascription; measure; body; range }
let mk_fn_decl id binders ascription range : fn_decl = { id; binders; ascription; range }
let mk_open lid = Open lid
let mk_par p1 p2 q1 q2 b1 b2 = Parallel { p1; p2; q1; q2; b1; b2 }
let mk_proof_hint_with_binders ht bs =  ProofHintWithBinders { hint_type=ht; binders=bs }
let mk_lambda bs ascription body range : lambda = { binders=bs; ascription; body; range }
let mk_with_invs names body returns_ = WithInvariants { names; body; returns_ }
