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
open FStarC
open FStarC.Ident
module A = FStarC.Parser.AST
module AD = FStarC.Parser.AST.Diff
open FStarC.Class.Show
open FStarC.Class.Tagged

let rng = FStarC.Range.range
let dummyRange = FStarC.Range.dummyRange

//Note: We do not yet process binder attributes, like typeclass attributes
type binder = A.binder
type binders = list binder

type slprop = A.term

type st_comp_tag = 
  | ST
  | STAtomic
  | STUnobservable
  | STGhost

type computation_annot' =
  | Preserves of slprop
  | Requires of slprop
  | Ensures of slprop
  | Returns of option ident & A.term
  | Opens of A.term

type computation_annot = computation_annot' & rng

type computation_type = {
     tag: st_comp_tag;
     annots : list computation_annot;
     range:rng
}

(* Not used in this module, but the list in annots above
is translated to this type before doing anything meaningful with it. *)
type parsed_annots = {
  precondition: slprop;
  postcondition: slprop;
  return_name: ident;
  return_type: A.term;
  opens: option A.term
}

type mut_or_ref =
  | MUT | REF

instance showable_mut_or_ref : showable mut_or_ref = {
  show = (fun i -> match i with
    | MUT -> "MUT"
    | REF -> "REF")
}

type hint_type =
  | ASSERT of slprop
  | ASSUME of slprop
  | UNFOLD of option (list lident) & slprop
  | FOLD of option (list lident) & slprop
  | RENAME of
      list (A.term & A.term) &
      option slprop & (* in goal *)
      option A.term (* optional tactic *)
  | REWRITE of
      slprop &
      slprop &
      option A.term (* optional tactic *)
  | WILD
  | SHOW_PROOF_STATE of rng

instance showable_hint_type : showable hint_type = {
  show = (fun i -> match i with
    | ASSERT s -> "ASSERT " ^ show s
    | ASSUME s -> "ASSUME " ^ show s
    | UNFOLD (ns, s) -> "UNFOLD " ^ show ns ^ " " ^ show s
    | FOLD (ns, s) -> "FOLD " ^ show ns ^ " " ^ show s
    | RENAME (ts, g, t) -> "RENAME " ^ show ts ^ " " ^ show g ^ " " ^ show t
    | REWRITE (s1, s2, t) -> "REWRITE " ^ show s1 ^ " " ^ show s2 ^ " " ^ show t
    | WILD -> "WILD"
    | SHOW_PROOF_STATE r -> "SHOW_PROOF_STATE ...")
}

type array_init = {
  init : A.term;
  len : A.term;
}

let ensures_slprop = option (ident & A.term) & slprop & option A.term

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
      norw:bool; (* add norewrite to the branch if this desugars to a match. *)
      qualifier: option mut_or_ref;
      pat:A.pattern;
      typ:option A.term;
      init:option let_init
    }
      
  | Block { 
      stmt : stmt
    }
    
  | If {
      head:A.term;
      join_slprop:option ensures_slprop;
      then_:stmt;
      else_opt:option stmt;
    }

  | Match {
      head:A.term;
      returns_annot:option ensures_slprop;
      branches:list (bool & A.pattern & stmt);
      (* ^ boolean true for 'norewrite' *)
    }

  | While {
      guard: stmt;
      id: option ident;
      invariant: slprop;
      body: stmt;
    }

  | Introduce {
      slprop:slprop;
      witnesses:list A.term
    }
      
  | Sequence {
      s1:stmt;
      s2:stmt;
    }

  | Parallel {
      p1:slprop;
      p2:slprop;
      q1:slprop;
      q2:slprop;
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
      returns_ : option ensures_slprop;
    }

and stmt = {
  s:stmt';
  range:rng;
  source:bool;
  (* true if this was written by the user, false for statements
  we generate automatically when desugaring. *)
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
  us:list ident;
  binders:binders;
  ascription:either computation_type (option A.term);
  measure:option A.term; // with binders in scope
  body:either stmt lambda;
  decorations:list A.decoration;  
  range:rng
}

and let_init =
  | Array_initializer of array_init
  | Default_initializer of A.term
  | Lambda_initializer of fn_defn
  | Stmt_initializer of stmt

instance showable_let_init : showable let_init = {
  show = (fun i -> match i with
    | Array_initializer a -> "Array_initializer ..."
    | Default_initializer t -> "Default_initializer ..."
    | Lambda_initializer l -> "Lambda_initializer ..."
    | Stmt_initializer s -> "Stmt_initializer ...")
}

type fn_decl = {
  id:ident;
  us:list ident;
  binders:binders;
  ascription:either computation_type (option A.term); (* always Inl for now *)
  decorations:list A.decoration;
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

instance tagged_stmt : Class.Tagged.tagged stmt = {
  tag_of = tag_of_stmt
}

let record_string (fs : list (string & string)) : string =
  "{" ^
  (String.concat "; " <| List.Tot.map (fun (f, s) -> f ^ " = " ^ s) fs) ^
  "}"

instance showable_pattern : showable A.pattern = {
  show = A.pat_to_string;
}

instance showable_a_term : showable A.term = {
  show = A.term_to_string;
}
instance showable_a_binder : showable A.binder = {
  show = A.binder_to_string;
}

let rec stmt_to_string (s:stmt) : string =
  match s.s with
  | Open l -> "Open " ^ show l
  | Expr {e} -> "Expr " ^ show e
  | Assignment { lhs; value } ->
    "Assignment " ^ record_string [
      "lhs", show lhs;
      "value", show value;
    ]
  | ArrayAssignment { arr; index; value } ->
    "ArrayAssignment " ^ record_string [
      "arr", show arr;
      "index", show index;
      "value", show value;
    ]
  | LetBinding { qualifier; pat; typ; init } ->
    "LetBinding " ^ record_string [
      "qualifier", show qualifier;
      "pat", show pat;
      "typ", show typ;
      "init", show init;
    ]
  | Block { stmt } ->
    "Block {" ^ stmt_to_string stmt ^ "}"
  | If { head; join_slprop; then_; else_opt } ->
    "If " ^ record_string [
      "head", show head;
      "join_slprop", show join_slprop;
      "then_", stmt_to_string then_;
      "else_opt", FStarC.Common.string_of_option stmt_to_string else_opt;
    ]
  | Match { head; returns_annot; branches } ->
    "Match " ^ record_string [
      "head", show head;
      "returns_annot", show returns_annot;
      "branches", FStarC.Common.string_of_list branch_to_string branches;
    ]
  | While { guard; id; invariant; body } ->
    "While " ^ record_string [
      "guard", stmt_to_string guard;
      "id", show id;
      "invariant", show invariant;
      "body", stmt_to_string body;
    ]
  | Introduce { slprop; witnesses } ->
    "Introduce " ^ record_string [
      "slprop", show slprop;
      "witnesses", FStarC.Common.string_of_list show witnesses
    ]
  | Sequence { s1; s2 } ->
    "Sequence " ^ record_string [
      "s1", stmt_to_string s1;
      "s2", stmt_to_string s2;
    ]
  | Parallel { p1; p2; q1; q2; b1; b2 } ->
    "Parallel " ^ record_string [
      "p1", show p1;
      "p2", show p2;
      "q1", show q1;
      "q2", show q2;
      "b1", stmt_to_string b1;
      "b2", stmt_to_string b2;
    ]
  | ProofHintWithBinders { hint_type; binders } ->
    "ProofHintWithBinders " ^ record_string [
      "hint_type", show hint_type;
      "binders", show binders;
    ]
  | WithInvariants { names; body; returns_ } ->
    "WithInvariants " ^ record_string [
      "names", FStarC.Common.string_of_list show names;
      "body", stmt_to_string body;
      "returns_", FStarC.Common.string_of_option show returns_;
    ]

and branch_to_string (b:bool & A.pattern & stmt) : string =
  let (norw, p, s) = b in
  show p ^ (if norw then "(norw)" else "") ^ " -> " ^ stmt_to_string s

instance showable_stmt : showable stmt = {
  show = stmt_to_string
}

type decl =
  | FnDefn of fn_defn
  | FnDecl of fn_decl
open FStarC.Class.Deq
let eq_ident (i1 i2:Ident.ident) = i1 =? i2
let eq_lident (i1 i2:Ident.lident) = i1 =? i2
let rec forall2 (f:'a -> 'a -> bool) (l1 l2:list 'a) : bool =
  match l1, l2 with
  | [], [] -> true
  | x::xs, y::ys -> f x y && forall2 f xs ys
  | _, _ -> false
let eq_opt (eq:'a -> 'a -> bool) (o1:option 'a) (o2:option 'a) =
  match o1, o2 with
  | Some x, Some y -> eq x y
  | None, None -> true
  | _, _ -> false
let rec eq_decl (d1 d2:decl) =
  match d1, d2 with
  | FnDefn f1, FnDefn f2 -> eq_fn_defn f1 f2
  | FnDecl d1, FnDecl d2 -> eq_fn_decl d1 d2
  | _ -> false
and eq_fn_decl (f1 f2:fn_decl) =
  eq_ident f1.id f2.id &&
  forall2 eq_ident f1.us f2.us &&
  forall2 AD.eq_binder f1.binders f2.binders &&
  eq_ascription f1.ascription f2.ascription
and eq_fn_defn (f1 f2:fn_defn) =
  eq_ident f1.id f2.id &&
  f1.is_rec = f2.is_rec &&
  forall2 eq_ident f1.us f2.us &&
  forall2 AD.eq_binder f1.binders f2.binders &&
  eq_ascription f1.ascription f2.ascription &&
  eq_opt AD.eq_term f1.measure f2.measure &&
  eq_body f1.body f2.body
and eq_ascription (a1 a2:either computation_type (option A.term)) =
  match a1, a2 with
  | Inl c1, Inl c2 -> eq_computation_type c1 c2
  | Inr t1, Inr t2 -> eq_opt AD.eq_term t1 t2
  | _, _ -> false
and eq_computation_type (c1 c2:computation_type) =
  c1.tag = c2.tag &&
  forall2 eq_annot c1.annots c2.annots
and eq_annot (a1 a2:computation_annot) =
  match fst a1, fst a2 with
  | Preserves s1, Preserves s2 -> eq_slprop s1 s2
  | Requires s1, Requires s2 -> eq_slprop s1 s2
  | Ensures s1, Ensures s2 -> eq_slprop s1 s2
  | Returns (i1, t1), Returns (i2, t2) -> eq_opt eq_ident i1 i2 && AD.eq_term t1 t2
  | Opens t1, Opens t2 -> AD.eq_term t1 t2
  | _, _ -> false
and eq_slprop (s1 s2 : slprop) =
  AD.eq_term s1 s2
and eq_body (b1 b2:either stmt lambda) =
  match b1, b2 with
  | Inl s1, Inl s2 -> eq_stmt s1 s2
  | Inr l1, Inr l2 -> eq_lambda l1 l2
  | _, _ -> false
and eq_stmt (s1 s2:stmt) =
  eq_stmt' s1.s s2.s
and eq_stmt' (s1 s2:stmt') =
  match s1, s2 with
  | Open l1, Open l2 -> eq_lident l1 l2
  | Expr e1, Expr e2 -> AD.eq_term e1.e e2.e
  | Assignment { lhs=l1; value=v1 }, Assignment { lhs=l2; value=v2 } ->
    AD.eq_term l1 l2 && AD.eq_term v1 v2
  | ArrayAssignment { arr=a1; index=i1; value=v1 }, ArrayAssignment { arr=a2; index=i2; value=v2 } ->
    AD.eq_term a1 a2 && AD.eq_term i1 i2 && AD.eq_term v1 v2
  | LetBinding { norw=norw1; qualifier=q1; pat=pat1; typ=t1; init=init1 }, LetBinding { norw=norw2; qualifier=q2; pat=pat2; typ=t2; init=init2 } ->
    norw1 = norw2 &&
    eq_opt eq_mut_or_ref q1 q2 &&
    AD.eq_pattern pat1 pat2 &&
    eq_opt AD.eq_term t1 t2 &&
    eq_opt eq_let_init init1 init2
  | Block { stmt=s1 }, Block { stmt=s2 } -> eq_stmt s1 s2
  | If { head=h1; join_slprop=j1; then_=t1; else_opt=e1 }, If { head=h2; join_slprop=j2; then_=t2; else_opt=e2 } ->
    AD.eq_term h1 h2 &&
    eq_opt eq_ensures_slprop j1 j2 &&
    eq_stmt t1 t2 &&
    eq_opt eq_stmt e1 e2
  | Match { head=h1; returns_annot=r1; branches=b1 }, Match { head=h2; returns_annot=r2; branches=b2 } ->
    AD.eq_term h1 h2 &&
    eq_opt eq_ensures_slprop r1 r2 &&
    forall2 (fun (norw1, p1, s1) (norw2, p2, s2) -> norw1 = norw2 && AD.eq_pattern p1 p2 && eq_stmt s1 s2) b1 b2
  | While { guard=g1; id=id1; invariant=i1; body=b1 }, While { guard=g2; id=id2; invariant=i2; body=b2 } ->
    eq_stmt g1 g2 &&
    eq_opt eq_ident id1 id2 &&
    eq_slprop i1 i2 &&
    eq_stmt b1 b2
  | Introduce { slprop=s1; witnesses=w1 }, Introduce { slprop=s2; witnesses=w2 } ->
    eq_slprop s1 s2 &&
    forall2 AD.eq_term w1 w2
  | Sequence { s1=s1; s2=s2 }, Sequence { s1=s1'; s2=s2' } ->
    eq_stmt s1 s1' && eq_stmt s2 s2'
  | Parallel { p1=p1; p2=p2; q1=q1; q2=q2; b1=b1; b2=b2 }, Parallel { p1=p1'; p2=p2'; q1=q1'; q2=q2'; b1=b1'; b2=b2' } ->
    eq_slprop p1 p1' &&
    eq_slprop p2 p2' &&
    eq_slprop q1 q1' &&
    eq_slprop q2 q2' &&
    eq_stmt b1 b1' &&
    eq_stmt b2 b2'
  | ProofHintWithBinders { hint_type=ht1; binders=bs1 }, ProofHintWithBinders { hint_type=ht2; binders=bs2 } ->
    eq_hint_type ht1 ht2 &&
    forall2 AD.eq_binder bs1 bs2
  | WithInvariants { names=n1; body=b1; returns_=r1 }, WithInvariants { names=n2; body=b2; returns_=r2 } ->
    forall2 AD.eq_term n1 n2 &&
    eq_stmt b1 b2 &&
    eq_opt eq_ensures_slprop r1 r2
  | _ -> false
and eq_let_init (i1 i2:let_init) =
  match i1, i2 with
  | Array_initializer a1, Array_initializer a2 -> eq_array_init a1 a2
  | Default_initializer t1, Default_initializer t2 -> AD.eq_term t1 t2
  | Lambda_initializer l1, Lambda_initializer l2 -> eq_fn_defn l1 l2
  | Stmt_initializer s1, Stmt_initializer s2 -> eq_stmt s1 s2
  | _, _ -> false
and eq_array_init (a1 a2:array_init) =
  AD.eq_term a1.init a2.init && AD.eq_term a1.len a2.len
and eq_hint_type (h1 h2:hint_type) =
  match h1, h2 with
  | ASSERT s1, ASSERT s2 -> eq_slprop s1 s2
  | ASSUME s1, ASSUME s2 -> eq_slprop s1 s2
  | UNFOLD (ns1, s1), UNFOLD (ns2, s2) ->
    eq_opt (forall2 eq_lident) ns1 ns2 &&
    eq_slprop s1 s2
  | FOLD (ns1, s1), FOLD (ns2, s2) ->
    eq_opt (forall2 eq_lident) ns1 ns2 &&
    eq_slprop s1 s2
  | RENAME (ts1, g1, t1), RENAME (ts2, g2, t2) ->
    forall2 (fun (t1, t2) (t1', t2') -> AD.eq_term t1 t1' && AD.eq_term t2 t2') ts1 ts2 &&
    eq_opt eq_slprop g1 g2 &&
    eq_opt AD.eq_term t1 t2
  | REWRITE (s1, s1', t1), REWRITE (s2, s2', t2) ->
    eq_slprop s1 s2 &&
    eq_slprop s1' s2' &&
    eq_opt AD.eq_term t1 t2
  | WILD, WILD -> true
  | SHOW_PROOF_STATE r1, SHOW_PROOF_STATE r2 -> true
  | _, _ -> false
and eq_ensures_slprop (e1 e2:ensures_slprop) =
  let h1, s1, t1 = e1 in
  let h2, s2, t2 = e2 in
  eq_opt (fun (i1, t1) (i2, t2) -> eq_ident i1 i2 && AD.eq_term t1 t2) h1 h2 &&
  eq_slprop s1 s2 &&
  eq_opt AD.eq_term t1 t2
and eq_lambda (l1 l2:lambda) =
  forall2 AD.eq_binder l1.binders l2.binders &&
  eq_opt eq_computation_type l1.ascription l2.ascription &&
  eq_stmt l1.body l2.body
and eq_mut_or_ref (m1 m2:mut_or_ref) =
  match m1, m2 with
  | MUT, MUT -> true
  | REF, REF -> true
  | _, _ -> false

let rec iter (f:'a -> unit) (l:list 'a) =
  match l with
  | [] -> ()
  | x::xs -> f x; iter f xs
let iopt (f:'a -> unit) (o:option 'a) =
  match o with
  | Some x -> f x
  | None -> ()
let ieither (f:'a -> unit) (g:'b -> unit) (e:either 'a 'b) =
  match e with
  | Inl x -> f x
  | Inr x -> g x
let rec scan_decl (cbs:A.dep_scan_callbacks) (d:decl) : unit =
  match d with
  | FnDefn f -> scan_fn_defn cbs f
  | FnDecl d -> scan_fn_decl cbs d
and scan_fn_decl (cbs:A.dep_scan_callbacks) (f:fn_decl) =
  iter (scan_binder cbs) f.binders;
  scan_ascription cbs f.ascription
and scan_fn_defn (cbs:A.dep_scan_callbacks) (f:fn_defn) =
  iter (scan_binder cbs) f.binders;
  ieither (scan_computation_type cbs) (iopt cbs.scan_term) f.ascription;
  iopt cbs.scan_term f.measure;
  ieither (scan_stmt cbs) (scan_lambda cbs) f.body
and scan_binder (cbs:A.dep_scan_callbacks) (b:binder) =
  cbs.scan_binder b
and scan_ascription (cbs:A.dep_scan_callbacks) (a:either computation_type (option A.term)) =
  ieither (scan_computation_type cbs) (iopt cbs.scan_term) a
and scan_computation_type (cbs:A.dep_scan_callbacks) (c:computation_type) =
  iter (scan_annot cbs) c.annots
and scan_annot cbs (a : computation_annot) =
  match fst a with
  | Preserves s -> scan_slprop cbs s
  | Requires s -> scan_slprop cbs s
  | Ensures s -> scan_slprop cbs s
  | Returns (i, t) -> cbs.scan_term t
  | Opens t -> cbs.scan_term t
and scan_slprop (cbs:A.dep_scan_callbacks) (s:slprop) =
  cbs.scan_term s
and scan_lambda (cbs:A.dep_scan_callbacks) (l:lambda) =
  iter (scan_binder cbs) l.binders;
  iopt (scan_computation_type cbs) l.ascription;
  scan_stmt cbs l.body
and scan_stmt (cbs:A.dep_scan_callbacks) (s:stmt) =
  match s.s with
  | Open l -> cbs.add_open l
  | Expr e -> cbs.scan_term e.e
  | Assignment { lhs=l; value=v } -> cbs.scan_term l; cbs.scan_term v
  | ArrayAssignment { arr=a; index=i; value=v } -> cbs.scan_term a; cbs.scan_term i; cbs.scan_term v
  | LetBinding { qualifier=q; pat=p; typ=t; init=init } ->
    iopt (scan_let_init cbs) init;
    cbs.scan_pattern p;
    iopt cbs.scan_term t
  | Block { stmt=s } -> scan_stmt cbs s
  | If { head=h; join_slprop=j; then_=t; else_opt=e } ->
    cbs.scan_term h;
    iopt (scan_ensures_slprop cbs) j;
    scan_stmt cbs t;
    iopt (scan_stmt cbs) e
  | Match { head=h; returns_annot=r; branches=b } ->
    cbs.scan_term h;
    iopt (scan_ensures_slprop cbs) r;
    iter (fun (_, p, s) -> cbs.scan_pattern p; scan_stmt cbs s) b
  | While { guard=g; id=id; invariant=i; body=b } ->
    scan_stmt cbs g;
    scan_slprop cbs i;
    scan_stmt cbs b
  | Introduce { slprop=s; witnesses=w } ->
    scan_slprop cbs s;
    iter cbs.scan_term w
  | Sequence { s1=s1; s2=s2 } -> scan_stmt cbs s1; scan_stmt cbs s2
  | Parallel { p1=p1; p2=p2; q1=q1; q2=q2; b1=b1; b2=b2 } ->
    scan_slprop cbs p1;
    scan_slprop cbs p2;
    scan_slprop cbs q1;
    scan_slprop cbs q2;
    scan_stmt cbs b1;
    scan_stmt cbs b2
  | ProofHintWithBinders { hint_type=ht; binders=bs } ->
    scan_hint_type cbs ht;
    iter (scan_binder cbs) bs
  | WithInvariants { names=n; body=b; returns_=r } ->
    iter cbs.scan_term n;
    scan_stmt cbs b;
    iopt (scan_ensures_slprop cbs) r
and scan_let_init (cbs:A.dep_scan_callbacks) (i:let_init) =
  match i with
  | Array_initializer a -> cbs.scan_term a.init; cbs.scan_term a.len
  | Default_initializer t -> cbs.scan_term t
  | Lambda_initializer l -> scan_fn_defn cbs l
  | Stmt_initializer s -> scan_stmt cbs s
and scan_ensures_slprop (cbs:A.dep_scan_callbacks) (e:ensures_slprop) =
  let h, s, t = e in
  iopt (fun (i, t) -> cbs.scan_term t) h;
  scan_slprop cbs s;
  iopt cbs.scan_term t
and scan_hint_type (cbs:A.dep_scan_callbacks) (h:hint_type) =
  match h with
  | ASSERT s -> scan_slprop cbs s
  | ASSUME s -> scan_slprop cbs s
  | UNFOLD (ns, s) -> scan_slprop cbs s
  | FOLD (ns, s) -> scan_slprop cbs s
  | RENAME (ts, g, t) -> iter (fun (t1, t2) -> cbs.scan_term t1; cbs.scan_term t2) ts; iopt (scan_slprop cbs) g; iopt cbs.scan_term t
  | REWRITE (s1, s2, t) -> scan_slprop cbs s1; scan_slprop cbs s2; iopt cbs.scan_term t
  | WILD -> ()
  | SHOW_PROOF_STATE _ -> ()

let range_of_decl (d:decl) =
  match d with
  | FnDefn f -> f.range
  | FnDecl d -> d.range
(* Convenience builders for use from OCaml/Menhir, since field names get mangled in OCaml *)
let mk_comp tag annots range =
  {
     tag;
     annots;
     range
  }
let add_decorations d ds =
  match d with
  | FnDefn f -> FnDefn { f with decorations=ds @ f.decorations }
  | FnDecl f -> FnDecl { f with decorations=ds @ f.decorations }
  
// let mk_slprop_exists binders body = SLPropExists { binders; body }
let mk_expr e = Expr { e }
let mk_assignment id value = Assignment { lhs=id; value }
let mk_array_assignment arr index value = ArrayAssignment { arr; index; value }
let mk_let_binding norw qualifier pat typ init = LetBinding { norw; qualifier; pat; typ; init }
let mk_block stmt = Block { stmt }
let mk_if head join_slprop then_ else_opt = If { head; join_slprop; then_; else_opt }
let mk_match head returns_annot branches = Match { head; returns_annot; branches }
let mk_while guard id invariant body = While { guard; id; invariant; body }
let mk_intro slprop witnesses = Introduce { slprop; witnesses }
let mk_sequence s1 s2 = Sequence { s1; s2 }
let mk_stmt s range = { s; range; source=true }
let mk_fn_defn id is_rec us binders ascription measure body decorations range
: fn_defn
= { id; is_rec; us; binders; ascription; measure; body; decorations; range }
let mk_fn_decl id us binders ascription decorations range
: fn_decl
= { id; us; binders; ascription; decorations; range }
let mk_open lid = Open lid
let mk_par p1 p2 q1 q2 b1 b2 = Parallel { p1; p2; q1; q2; b1; b2 }
let mk_proof_hint_with_binders ht bs =  ProofHintWithBinders { hint_type=ht; binders=bs }
let mk_lambda bs ascription body range : lambda = { binders=bs; ascription; body; range }
let mk_with_invs names body returns_ = WithInvariants { names; body; returns_ }
