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

open FStar.Preorder
open FStar.ReflexiveTransitiveClosure
open FStar.WellFounded


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


let lex_wf #_ #_ #_ #_ wf_a wf_b =
  fun (| x, y |) -> AccIntro (lex_wf_aux x (wf_a x) wf_b y (wf_b x y))

open FStar.Squash

(*
 * Given lex_sq, we can output a squashed instance of lex
 *)
let lex_sq_to_lex #a #b r_a r_b t1 t2 p =
  let left (p:squash (r_a (dfst t1) (dfst t2)))
    : squash (lex r_a r_b t1 t2)
    = bind_squash p (fun p ->
        return_squash (Left_lex #a #b #r_a #r_b (dfst t1) (dfst t2) (dsnd t1) (dsnd t2) p)) in

  let right (p:(dfst t1 == dfst t2 /\ (squash (r_b (dfst t1) (dsnd t1) (dsnd t2)))))
    : squash (lex r_a r_b t1 t2)
    = bind_squash p (fun p ->
        match p with
        | And (_:dfst t1 == dfst t2) p2 ->
          bind_squash p2 (fun p2 ->
            return_squash (Right_lex #a #b #r_a #r_b (dfst t1) (dsnd t1) (dsnd t2) p2))) in

  bind_squash p (fun p ->
    match p with
    | Left p1 -> left p1
    | Right p2 -> right p2)



/// Proof for well-foundedness of symmetric products
///
/// The proof follows the same structure as for the lex ordering

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

let sym_wf #_ #_ #_ #_ wf_a wf_b =
  fun (x, y) -> AccIntro (sym_wf_aux x (wf_a x) y (wf_b y))



/// Let's now use `lex` to prove termination for the ackermann function
///
/// F* supports user-defined well-foundned orderings in the decreases clauses
///
/// However, since those proofs are SMT-based, instead of working with the
///   constructive lex relation, we work with the squashed version,

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
             (lex_sq lt_well_founded lt_dep_well_founded)
             (| m, n |) })
  = if m = 0 then n + 1
    else if n = 0 then ackermann (m - 1) 1
    else ackermann (m - 1) (ackermann m (n - 1))
