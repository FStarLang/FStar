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
#set-options "--warn_error -242" //no inner let recs in SMT
open FStar.ReflexiveTransitiveClosure
open FStar.WellFounded

/// A helper lemma about reflexive transitive closure

let closure_transitive (#a:Type u#a) (#r_a:binrel u#a a) (x y z:a)
  : Lemma
      (requires closure r_a x y /\
                r_a y z)
      (ensures  closure r_a x z)
      [SMTPat (closure r_a x y);
       SMTPat (r_a y z)]
  = assert (closure r_a y z)

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

let rec lex_t_wf_aux (#a:Type u#a)
                     (#b:a -> Type u#b)
                     (#r_a:binrel u#a a)
                     (#r_b:(x:a -> binrel u#b (b x)))
                     (x:a)
                     (acc_x:acc r_a x)  //x and accessibility of x
                     (wf_b:(x0:a{closure r_a x0 x} -> well_founded (r_b x0)))  //well-foundedness of r_b
                     (y:b x)
                     (acc_y:acc (r_b x) y)  //y and accessibility of y
                     (t:(x:a & b x))  //another element t,
                     (p_t:lex_t r_a r_b t (| x, y |))  //that is related to (| x, y |)
  : Tot (acc (lex_t r_a r_b) t)  //returns the accessibility proof for t
        (decreases acc_x)
  = let (| x_t, y_t |) = t in
    if r_a x_t x then
      let p_a: r_a x_t x = () in
      AccIntro (lex_t_wf_aux
        x_t
        (match acc_x with
         | AccIntro f -> f x_t p_a)
        wf_b
        y_t
        (wf_b x_t y_t))
    else begin
      assert x_t == x /\ r_b x y_t y;
      let rec lex_t_wf_aux_y (y:b x) (acc_y:acc (r_b x) y) (t:(x:a & b x)) (p_t:lex_t r_a r_b t (| x, y |))
        : Tot (acc (lex_t r_a r_b) t)
              (decreases acc_y)
        = let (| x_t, y_t |) = t in
          if r_a x_t x then
            let p_a: r_a x_t x = () in
            AccIntro (lex_t_wf_aux
              x_t
              (match acc_x with
               | AccIntro f -> f x_t p_a)
              wf_b
              y_t
              (wf_b x_t y_t))
          else
            let p_b: r_b x y_t y = () in
            AccIntro (lex_t_wf_aux_y
              y_t
              (match acc_y with
               | AccIntro f -> f y_t p_b)) in
      lex_t_wf_aux_y y acc_y t p_t
    end


let lex_t_wf #_ #_ #_ #_ wf_a wf_b =
  fun (| x, y |) -> AccIntro (lex_t_wf_aux x (wf_a x) wf_b y (wf_b x y))

let lex_t_non_dep_wf #a #b #r_a #r_b wf_a wf_b =
  let rec get_acc (t:a & b) (p:acc (lex_t r_a (fun _ -> r_b)) (tuple_to_dep_tuple t))
    : Tot (acc (lex_t_non_dep r_a r_b) t)
          (decreases p)
    = let get_acc_aux (t1:a & b) (p_dep:lex_t_non_dep r_a r_b t1 t)
        : (p1:acc (lex_t r_a (fun _ -> r_b)) (tuple_to_dep_tuple t1){p1 << p})
        = match p with
          | AccIntro f -> f (tuple_to_dep_tuple t1) p_dep in
      AccIntro (fun t1 p1 -> get_acc t1 (get_acc_aux t1 p1)) in
  fun t -> get_acc t (lex_t_wf wf_a (fun _ -> wf_b) (tuple_to_dep_tuple t))
