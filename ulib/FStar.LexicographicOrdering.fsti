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

/// This module proves that lexicographic ordering is well-founded
///   (i.e. every element is accessible)
///
/// It defines the lex relation as an inductive, and prove its well-foundedness
///
/// Since SMT proofs in F* are more amenable to squashed definitions,
///   the module also defines a squashed version of the lex relation,
///   and prove its well-foundedness, reusing the proof for the constructive version
///
/// See tests/micro-benchmarks/Test.WellFoundedRecursion.fst for
///   how we use squashed `lex` to prove termination for the ackermann function
///
/// Finally, the module defines a non-dependent version of lex
///   (in-terms of dependent lex), and uses it to prove well-foundedness of symmetric products too
/// 
/// Some references:
///   - https://github.com/coq/coq/blob/master/theories/Wellfounded/Lexicographic_Product.v
///   - Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355

open FStar.WellFounded
open FStar.Nonempty


/// Definition of lexicographic ordering as a relation over dependent tuples
///
/// Two elements are related if:
///   - Either their first components are related
///   - Or, the first components are equal, and the second components are related

let lex_t (#a:Type u#a) (#b:a -> Type u#b)
  (r_a:binrel u#a a)
  (r_b:(x:a -> binrel u#b (b x)))
  : binrel u#(max a b) (x:a & b x)
  = fun (| x1, y1 |) (| x2, y2 |) ->
    r_a x1 x2 \/
    (x1 == x2 /\ r_b x1 y1 y2)

/// Given two well-founded relations `r_a` and `r_b`,
///   their lexicographic ordering is also well-founded

val lex_t_wf (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a a)
  (#r_b:(x:a -> binrel u#b (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded (lex_t r_a r_b)

/// And prove that is it is well-founded

let lex_wf (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a a)
  (#r_b:(x:a -> binrel u#b (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : Lemma (is_well_founded (lex_t r_a r_b))
  = is_well_founded_of_well_founded (lex_t_wf wf_a wf_b)


/// A user-friendly lex_wf that returns a well-founded relation

unfold
let lex (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a a)
  (#r_b:(x:a -> binrel u#b (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded_relation (x:a & b x)
  = lex_wf wf_a wf_b;
    lex_t r_a r_b


/// We can also define a non-dependent version of the lex ordering,
///   in terms of the dependent lex tuple,
///   and prove its well-foundedness

let tuple_to_dep_tuple (#a #b:Type) (x:a & b) : dtuple2 a (fun _ -> b) =
  (| fst x, snd x |)


/// The non-dependent lexicographic ordering
///   and its well-foundedness

let lex_t_non_dep (#a:Type u#a) 
                  (#b:Type u#b)
                  (r_a:binrel u#a a)
                  (r_b:binrel u#b b)
  : binrel u#(max a b) (a & b)
  = fun x y ->
      lex_t r_a (fun _ -> r_b) (tuple_to_dep_tuple x) (tuple_to_dep_tuple y)

val lex_t_non_dep_wf (#a:Type u#a)
                     (#b:Type u#b)
                     (#r_a:binrel u#a a)
                     (#r_b:binrel u#b b)
                     (wf_a:well_founded r_a)
                     (wf_b:well_founded r_b)
  : well_founded (lex_t_non_dep r_a r_b)


/// Symmetric product relation
///   we can prove its well-foundedness by showing that it is a subrelation of non-dep lex

let sym (#a:Type u#a) (#b:Type u#b) (r_a:binrel u#a a) (r_b:binrel u#b b)
    (x: a & b) (y : a & b) : prop =
  (snd x == snd y /\ r_a (fst x) (fst y)) \/
  (fst x == fst y /\ r_b (snd x) (snd y))

/// sym is a subrelation of non-dependent lex

let sym_sub_lex (#a:Type u#a)
                (#b:Type u#b)
                (#r_a:binrel u#a a)
                (#r_b:binrel u#b b)
                (t1 t2:a & b)
                (p:sym r_a r_b t1 t2)
  : lex_t_non_dep r_a r_b t1 t2
  = ()

/// Theorem for symmetric product
///
let sym_wf (#a:Type u#a)
           (#b:Type u#b)
           (#r_a:binrel u#a a)
           (#r_b:binrel u#b b)
           (wf_a:well_founded r_a)
           (wf_b:well_founded r_b)
  : well_founded (sym r_a r_b)
  = subrelation_wf sym_sub_lex (lex_t_non_dep_wf wf_a wf_b)
