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


/// Definition of lexicographic ordering as a relation over dependent tuples
///
/// Two elements are related if:
///   - Either their first components are related
///   - Or, the first components are equal, and the second components are related

noeq
type lex_t (#a:Type u#a) (#b:a -> Type u#b) 
           (r_a:binrel u#a u#ra a)
           (r_b:(x:a -> binrel u#b u#rb (b x)))
  : (x:a & b x) -> (x:a & b x) -> Type u#(max a b ra rb) =
  | Left_lex:
    x1:a -> x2:a ->
    y1:b x1 -> y2:b x2 ->
    r_a x1 x2 ->
    lex_t r_a r_b (| x1, y1 |) (| x2, y2 |)
  | Right_lex:
    x:a ->
    y1:b x -> y2:b x ->
    r_b x y1 y2 ->
    lex_t r_a r_b (| x, y1 |) (| x, y2 |)

/// Given two well-founded relations `r_a` and `r_b`,
///   their lexicographic ordering is also well-founded

val lex_t_wf (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a u#ra a)
  (#r_b:(x:a -> binrel u#b u#rb (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded (lex_t r_a r_b)


/// We can also define a squashed version of lex relation

unfold
let lex_aux (#a:Type u#a) (#b:a -> Type u#b)
  (r_a:binrel u#a u#ra a)
  (r_b:(x:a -> binrel u#b u#rb (b x)))
  : binrel u#(max a b) u#0 (x:a & b x)
  = fun (| x1, y1 |) (| x2, y2 |) ->
    (squash (r_a x1 x2)) \/
    (x1 == x2 /\ squash ((r_b x1) y1 y2))


/// Provide a mapping from a point in lex_aux to a squashed point in lex

val lex_to_lex_t (#a:Type u#a) (#b:a -> Type u#b)
  (r_a:binrel u#a u#ra a)
  (r_b:(x:a -> binrel u#b u#rb (b x)))
  (t1 t2:(x:a & b x))
  (p:lex_aux r_a r_b t1 t2)
  : squash (lex_t r_a r_b t1 t2)

/// And prove that is it is well-founded

let lex_wf (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a u#ra a)
  (#r_b:(x:a -> binrel u#b u#rb (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : Lemma (is_well_founded (lex_aux r_a r_b))
  = subrelation_squash_wf (lex_to_lex_t r_a r_b) (lex_t_wf wf_a wf_b)


/// A user-friendly lex_wf that returns a well-founded relation

unfold
let lex (#a:Type u#a) (#b:a -> Type u#b)
  (#r_a:binrel u#a u#ra a)
  (#r_b:(x:a -> binrel u#b u#rb (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded_relation (x:a & b x)
  = lex_wf wf_a wf_b;
    lex_aux r_a r_b


/// We can also define a non-dependent version of the lex ordering,
///   in terms of the dependent lex tuple,
///   and prove its well-foundedness

let tuple_to_dep_tuple (#a #b:Type) (x:a & b) : dtuple2 a (fun _ -> b) =
  (| fst x, snd x |)


/// The non-dependent lexicographic ordering
///   and its well-foundedness

let lex_t_non_dep (#a:Type u#a) 
                  (#b:Type u#b)
                  (r_a:binrel u#a u#ra a)
                  (r_b:binrel u#b u#rb b)
  : binrel u#(max a b) u#(max a b ra rb) (a & b)
  = fun x y ->
      lex_t r_a (fun _ -> r_b) (tuple_to_dep_tuple x) (tuple_to_dep_tuple y)

val lex_t_non_dep_wf (#a:Type u#a)
                     (#b:Type u#b)
                     (#r_a:binrel u#a u#ra a)
                     (#r_b:binrel u#b u#rb b)
                     (wf_a:well_founded r_a)
                     (wf_b:well_founded r_b)
  : well_founded (lex_t_non_dep r_a r_b)


/// Symmetric product relation
///   we can prove its well-foundedness by showing that it is a subrelation of non-dep lex

noeq
type sym (#a:Type u#a)
         (#b:Type u#b)
         (r_a:binrel u#a u#ra a)
         (r_b:binrel u#b u#rb b)
  : (a & b) -> (a & b) -> Type u#(max a b ra rb) =  
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

/// sym is a subrelation of non-dependent lex

let sym_sub_lex (#a:Type u#a)
                (#b:Type u#b)
                (#r_a:binrel u#a u#ra a)
                (#r_b:binrel u#b u#rb b)
                (t1 t2:a & b)
                (p:sym r_a r_b t1 t2)
  : lex_t_non_dep r_a r_b t1 t2
  = match p with
    | Left_sym x1 x2 y p ->
      Left_lex #a #(fun _ -> b) #r_a #(fun _ -> r_b) x1 x2 y y p
    | Right_sym x y1 y2 p ->
      Right_lex #a #(fun _ -> b) #r_a #(fun _ -> r_b) x y1 y2 p


/// Theorem for symmetric product
///
let sym_wf (#a:Type u#a)
           (#b:Type u#b)
           (#r_a:binrel u#a u#ra a)
           (#r_b:binrel u#b u#rb b)
           (wf_a:well_founded r_a)
           (wf_b:well_founded r_b)
  : well_founded (sym r_a r_b)
  = subrelation_wf sym_sub_lex (lex_t_non_dep_wf wf_a wf_b)
