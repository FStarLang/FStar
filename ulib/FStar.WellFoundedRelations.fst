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

module FStar.WellFoundedRelations

/// This module proves that lexicographic and symmetric products are
///   well-founded (i.e. every element is accessible)
///
/// The main theorems in the module are `lex_wf` and `sym_wf`
///
/// Towards the end, we use `lex` to prove termination for the ackermann function
/// 
/// Some references:
///   - https://github.com/coq/coq/blob/master/theories/Wellfounded/Lexicographic_Product.v
///   - Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355

open FStar.Preorder
open FStar.ReflexiveTransitiveClosure
open FStar.WellFounded


/// Abbreviations for FStar.WellFounded.well_founded and
///   FStar.WellFounded.acc with the first argument an implicit

type acc (#a:Type) (rel:relation a) (x:a) = acc a rel x
type well_founded (#a:Type) (rel:relation a) = well_founded a rel


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


/// A helper lemma about reflexive transitive closure

let closure_transitive (#a:Type) (#r_a:relation a) (x y z:a)
  : Lemma
      (requires (closure r_a) x y /\ r_a y z)
      (ensures (closure r_a) x z)
      [SMTPat ((closure r_a) x y); SMTPat (r_a y z)]
  = assert ((closure r_a) y z)


/// The main workhorse for the proof of lex_t well-foundedness
///
/// Given x:a and (y:b x), along with proof of their accessibility,
///   this function provides a proof of accessibility for all t s.t. lex_t t (| x, y |)
///
/// The proof is by induction on the accessibility proofs of x and y
///   In the Left_lex case, we do the induction on the accessibility of x,
///   and in the Right_lex case, on the accessibility of y
///
/// Note also that the proof _does not_ rely on the in-built lexicographic ordering in F*
///
/// An interesting aspect of the proof is the wf_b argument,
///   that provides a proof for the well-foundedness of r_b,
///   but note that we only require it on elements of a that are related to x in the
///   transitive closure of r_a

let rec lex_wf_aux (#a:Type) (#b:a -> Type) (#r_a:relation a) (#r_b:(x:a -> relation (b x)))
  (x:a) (acc_x:acc r_a x)  //x and accessibility of x
  (wf_b:(x0:a{(closure r_a) x0 x} -> well_founded (r_b x0)))  //well-foundedness of r_b
  (y:b x) (acc_y:acc (r_b x) y)  //y and accessibility of y
  (t:(x:a & b x))  //another element t,
  (p_t:lex r_a r_b t (| x, y |))  //that is related to (| x, y |)
  : Tot (acc (lex r_a r_b) t)  //returns the accessibility proof for t
        (decreases acc_x)
  = match p_t with
    | Left_lex x_t _ y_t _ p_a ->
      AccIntro (lex_wf_aux
        x_t
        (match acc_x with
         | AccIntro f -> f x_t p_a)
        wf_b
        y_t
        (wf_b x_t y_t))
    | Right_lex _ _ _ _ ->
      //inner induction that keeps x same, but recurses on acc_y
      let rec lex_wf_aux_y (y:b x) (acc_y:acc (r_b x) y) (t:(x:a & b x)) (p_t:lex r_a r_b t (| x, y |))
        : Tot (acc (lex r_a r_b) t)
              (decreases acc_y)
        = match p_t with
          | Left_lex x_t _ y_t _ p_a ->
            AccIntro (lex_wf_aux
              x_t
              (match acc_x with
               | AccIntro f -> f x_t p_a)
              wf_b
              y_t
              (wf_b x_t y_t))
          | Right_lex _ y_t _ p_b ->
            AccIntro (lex_wf_aux_y
              y_t
              (match acc_y with
               | AccIntro f -> f y_t p_b)) in
      lex_wf_aux_y y acc_y t p_t


/// Main theorem
///
/// Given two well-founded relations `r_a` and `r_b`,
///   their lexicographic ordering is also well-founded

let lex_wf (#a:Type) (#b:a -> Type)
  (r_a:relation a)
  (r_b:(x:a -> relation (b x)))
  (wf_a:well_founded r_a)
  (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded (lex r_a r_b)
  = fun (| x, y |) ->
    AccIntro (lex_wf_aux x (wf_a x) wf_b y (wf_b x y))


/// Proof for well-foundedness of symmetric products
///
/// The proof follows the same structure as for the lex ordering


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

let rec sym_wf_aux (#a #b:Type) (#r_a:relation a) (#r_b:relation b)
  (x:a) (acc_a:acc r_a x)
  (y:b) (acc_b:acc r_b y)
  (t:a & b)
  (p_t:sym r_a r_b t (x, y))
  : Tot (acc (sym r_a r_b) t)
        (decreases acc_a)
  = match p_t with
    | Left_sym x_t _ _ p_a ->
      AccIntro (sym_wf_aux
        x_t
        (match acc_a with
         | AccIntro f -> f x_t p_a)
        y
        acc_b)
    | Right_sym _ _ _ _ ->
      let rec sym_wf_aux_y (y:b) (acc_b:acc r_b y) (t:a & b) (p_t:sym r_a r_b t (x, y))
        : Tot (acc (sym r_a r_b) t)
              (decreases acc_b)
        = match p_t with
         | Left_sym x_t _ _ p_a ->
           AccIntro (sym_wf_aux
             x_t
             (match acc_a with
              | AccIntro f -> f x_t p_a)
             y
             acc_b)
         | Right_sym _ y_t _ p_b ->
           AccIntro (sym_wf_aux_y
             y_t
             (match acc_b with
              | AccIntro f -> f y_t p_b)) in
      sym_wf_aux_y y acc_b t p_t


/// Main theorem for symmetric product

let sym_wf (#a #b:Type)
  (r_a:relation a)
  (r_b:relation b)
  (wf_a:well_founded r_a)
  (wf_b:well_founded r_b)
  : well_founded (sym r_a r_b)
  = fun (x, y) -> AccIntro (sym_wf_aux x (wf_a x) y (wf_b y))



/// Let's now use `lex` to prove termination for the ackermann function
///
/// F* supports user-defined well-foundned orderings in the decreases clauses///
///
/// However, since those proofs are SMT-based, to use our `lex` relation,
///   we need to define a `squash` version of it

open FStar.Squash


/// The Left_lex constructor in the squashed world

let lex_squash_left (#a:Type) (#b:a -> Type)
  (r_a:relation a)
  (r_b:(x:a -> relation (b x)))
  (x1:a) (y1:b x1)
  (x2:a) (y2:b x2)
  (p:squash (r_a x1 x2))
  : Lemma (squash (lex r_a r_b (| x1, y1 |) (| x2, y2 |)))
  = bind_squash p (fun t -> return_squash (Left_lex #a #b #r_a #r_b x1 x2 y1 y2 t))

///
/// The Right_lex constructor analogously

let lex_squash_right (#a:Type) (#b:a -> Type)
  (r_a:relation a)
  (r_b:(x:a -> relation (b x)))
  (x:a) (y1:b x)
  (y2:b x)
  (p:squash (r_b x y1 y2))
  : Lemma (squash (lex r_a r_b (| x, y1 |) (| x, y2 |)))
  = bind_squash p (fun t -> return_squash (Right_lex #a #b #r_a #r_b x y1 y2 t))


/// Combine the two

#push-options "--warn_error -271"
let lex_squash  (#a:Type) (#b:a -> Type)
  (r_a:relation a)
  (r_b:(x:a -> relation (b x)))
  : Lemma
      ((forall (x1:a) (x2:a) (y1:b x1) (y2:b x2).{:pattern lex r_a r_b (| x1, y1 |) (| x2, y2 |)}
          squash (r_a x1 x2) ==> squash (lex r_a r_b (| x1, y1 |) (| x2, y2 |))) /\
       (forall (x:a) (y1:b x) (y2:b x).{:pattern lex r_a r_b (| x, y1 |) (| x, y2 |)}
          squash (r_b x y1 y2) ==> squash (lex r_a r_b (| x, y1 |) (| x, y2 |))))
  = let left
      (x1:a) (y1:b x1)
      (x2:a) (y2:b x2)
      : Lemma (squash (r_a x1 x2) ==> squash (lex r_a r_b (| x1, y1 |) (| x2, y2 |)))
              [SMTPat ()]
      = Classical.impl_intro (lex_squash_left r_a r_b x1 y1 x2 y2) in
    let right (x:a) (y1:b x) (y2:b x)
      : Lemma (squash (r_b x y1 y2) ==> squash (lex r_a r_b (| x, y1 |) (| x, y2 |)))
              [SMTPat ()]
      = Classical.impl_intro (lex_squash_right r_a r_b x y1 y2) in
    ()
#pop-options



/// Let's build towards ackermann

unfold
let lt : relation nat = fun x y -> x < y

unfold
let lt_dep (_:nat) : relation nat = fun x y -> x < y

let rec lt_well_founded (n:nat) : acc lt n =
  AccIntro (fun m _ -> lt_well_founded m)

let rec lt_dep_well_founded (m:nat) (n:nat) : acc (lt_dep m) n =
  AccIntro (fun p _ -> lt_dep_well_founded m p)

let rec ackermann (m n:nat)
  : Tot nat (decreases {:well-founded
             (as_well_founded (lex lt lt_dep) (lex_wf lt lt_dep lt_well_founded lt_dep_well_founded))
             (| m, n |) })
  = lex_squash lt lt_dep;
    if m = 0 then n + 1
    else if n = 0 then ackermann (m - 1) 1
    else ackermann (m - 1) (ackermann m (n - 1))
