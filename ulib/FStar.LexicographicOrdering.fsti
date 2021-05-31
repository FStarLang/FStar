(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Aseem Rastogi and Nikhil Swamy
*)

module FStar.LexicographicOrdering

/// This module proves that lexicographic and symmetric products are
///   well-founded (i.e. every element is accessible)
///
/// The main theorems in the module are `lex_wf` and `sym_wf`
///
/// See FStar.LexicographicOrdering.fst for how we use `lex` to prove termination for the ackermann function
/// 
/// Some references:
///   - https://github.com/coq/coq/blob/master/theories/Wellfounded/Lexicographic_Product.v
///   - Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355

open FStar.Preorder
open FStar.WellFounded


/// Definition of lexicographic ordering as a relation over dependent tuples
///
/// Two elements are related if:
///   - Either their first components are related
///   - Or, the first components are equal, and the second components are related

noeq
type lex (#a:Type) (#b:a -> Type) (r_a:relation a) (r_b:(x:a -> relation (b x)))
  : (x:a & b x) -> (x:a & b x) -> Type =
  | Left_lex:
    x1:a -> x2:a ->
    y1:b x1 -> y2:b x2 ->
    r_a x1 x2 ->
    lex r_a r_b (| x1, y1 |) (| x2, y2 |)
  | Right_lex:
    x:a ->
    y1:b x -> y2:b x ->
    r_b x y1 y2 ->
    lex r_a r_b (| x, y1 |) (| x, y2 |)

/// Given two well-founded relations `r_a` and `r_b`,
///   their lexicographic ordering is also well-founded

val lex_wf (#a:Type) (#b:a -> Type)
  (#r_a:relation a)
  (#r_b:(x:a -> relation (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded (lex r_a r_b)


/// We can also define a squashed version of lex relation

unfold
let lex_sq_aux (#a:Type) (#b:a -> Type)
  (r_a:relation a)
  (r_b:(x:a -> relation (b x)))
  ((| x1, y1 |):(x:a & b x))
  ((| x2, y2 |):(x:a & b x)) =
  (squash (r_a x1 x2)) \/
  (x1 == x2 /\ squash ((r_b x1) y1 y2))


/// Provide a mapping from a point in lex_sq to a squashed point in lex

val lex_sq_to_lex (#a:Type) (#b:a -> Type)
  (r_a:relation a)
  (r_b:(x:a -> relation (b x)))
  (t1 t2:(x:a & b x))
  (p:lex_sq_aux r_a r_b t1 t2)
  : squash (lex r_a r_b t1 t2)

/// And prove that is it is well-founded

let lex_sq_wf (#a:Type) (#b:a -> Type)
  (#r_a:relation a)
  (#r_b:(x:a -> relation (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : Lemma (is_well_founded (lex_sq_aux r_a r_b))
  = map_squash_is_well_founded (lex_sq_to_lex r_a r_b) (lex_wf wf_a wf_b)


/// A user-friendly lex_wf that returns a well-founded relation

unfold
let lex_sq (#a:Type) (#b:a -> Type)
  (#r_a:relation a)
  (#r_b:(x:a -> relation (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded_relation (x:a & b x)
  = lex_sq_wf wf_a wf_b;
    lex_sq_aux r_a r_b


/// Symmetric product relation

noeq
type sym (#a:Type) (#b:Type) (r_a:relation a) (r_b:relation b)
  : (a & b) -> (a & b) -> Type =  
  | Left_sym:
    x1:a -> x2:a ->
    y:b ->
    r_a x1 x2 ->
    sym r_a r_b (x1, y) (x2, y)
  | Right_sym:
    x:a ->
    y1:b -> y2:b ->
    r_b y1 y2 ->
    sym r_a r_b (x, y1) (x, y2)

/// Theorem for symmetric product

val sym_wf (#a #b:Type)
  (#r_a:relation a)
  (#r_b:relation b)
  (wf_a:well_founded r_a)
  (wf_b:well_founded r_b)
  : well_founded (sym r_a r_b)
