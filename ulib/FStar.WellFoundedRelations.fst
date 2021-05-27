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
*)

module FStar.WellFoundedRelations

open FStar.WellFounded

noeq
type lex_t (#a:Type) (#b:a -> Type) (r_a:a -> a -> Type) (r_b:(x:a -> b x -> b x -> Type))
  : (x:a & b x) -> (x:a & b x) -> Type =

  | Left_lex : x1:a -> x2:a -> y1:b x1 -> y2:b x2 -> r_a x1 x2 -> lex_t r_a r_b (| x1, y1 |) (| x2, y2 |)
  | Right_lex: x:a -> y1:b x -> y2:b x -> r_b x y1 y2 -> lex_t r_a r_b (| x, y1 |) (| x, y2 |)

(* private *)
let rec acc_lexprod_aux (#a:Type) (#b:a -> Type) (#r_a:a -> a -> Type) (#r_b:(x:a -> b x -> b x -> Type))
  (x:a) (acc_x:acc a r_a x)
  (wf_b:(x0:a -> y0:b x0 -> acc (b x0) (r_b x0) y0))
  (y:b x) (acc_y:acc (b x) (r_b x) y)
  (t:(x:a & b x))
  (p_t:lex_t r_a r_b t (| x, y |))
  : Tot (acc (x:a & b x) (lex_t r_a r_b) t)
        (decreases acc_x)
  = match p_t with
    | Left_lex x_t _ y_t _ p_a ->
      AccIntro (acc_lexprod_aux
        x_t
        (match acc_x with
         | AccIntro f -> f x_t p_a)
        wf_b
        y_t
        (wf_b x_t y_t))
    | Right_lex _ _ _ _ ->
      let rec aux (y:b x) (acc_y:acc (b x) (r_b x) y) (t:(x:a & b x)) (p_t:lex_t r_a r_b t (| x, y |))
        : Tot (acc (x:a & b x) (lex_t r_a r_b) t)
              (decreases acc_y)
        = match p_t with
          | Left_lex x_t _ y_t _ p_a ->
            AccIntro (acc_lexprod_aux
              x_t
              (match acc_x with
               | AccIntro f -> f x_t p_a)
              wf_b
              y_t
              (wf_b x_t y_t))
          | Right_lex _ y_t _ p_b ->
            AccIntro (aux
              y_t
              (match acc_y with
               | AccIntro f -> f y_t p_b)) in
      aux y acc_y t p_t

(* private *)
let acc_lexprod (#a:Type) (#b:a -> Type) (#r_a:a -> a -> Type) (#r_b:(x:a -> b x -> b x -> Type))
  (x:a) (acc_x:acc a r_a x)
  (wf_b:(x0:a -> y0:b x0 -> acc (b x0) (r_b x0) y0))
  (y:b x) (acc_y:acc (b x) (r_b x) y)
  : acc (x:a & b x) (lex_t r_a r_b) (| x, y |)
  = AccIntro (acc_lexprod_aux x acc_x wf_b y acc_y)

(* private *)
let lex_t_wf_aux (#a:Type) (#b:a -> Type) (#r_a:a -> a -> Type) (#r_b:(x:a -> b x -> b x -> Type))
  (wf_a:(x:a -> acc a r_a x))
  (wf_b:(x:a -> y:b x -> acc (b x) (r_b x) y))
  (t1:(x:a & b x))
  (t2:(x:a & b x))
  (p:lex_t r_a r_b t2 t1)
  : acc (x:a & b x) (lex_t r_a r_b) t2
  = let (| x2, y2 |) = t2 in
    acc_lexprod x2 (wf_a x2) wf_b y2 (wf_b x2 y2)

(* main theorem *)
let lex_t_wf (#a:Type) (#b:a -> Type)
  (r_a:a -> a -> Type)
  (r_b:(x:a -> b x -> b x -> Type))
  (wf_a:well_founded a r_a)
  (wf_b:(x:a -> well_founded (b x) (r_b x)))
  : well_founded (x:a & b x) (lex_t r_a r_b)
  = fun t -> AccIntro (lex_t_wf_aux wf_a wf_b t)
    

noeq
type sym_t (#a:Type) (#b:Type) (r_a:a -> a -> Type) (r_b:b -> b -> Type)
  : (a & b) -> (a & b) -> Type =
  
  | Left_sym  : x1:a -> x2:a -> y:b -> r_a x1 x2 -> sym_t r_a r_b (x1, y) (x2, y)
  | Right_sym : x:a -> y1:b -> y2:b -> r_b y1 y2 -> sym_t r_a r_b (x, y1) (x, y2)

let rec symprod_wf_aux (#a #b:Type) (#r_a:a -> a -> Type) (#r_b:b -> b -> Type)
  (x:a) (acc_a:acc a r_a x)
  (y:b) (acc_b:acc b r_b y)
  (t:a & b)
  (p_t:sym_t r_a r_b t (x, y))
  : Tot (acc (a & b) (sym_t r_a r_b) t)
        (decreases acc_a)
  = match p_t with
    | Left_sym x_t _ _ p_a ->
      AccIntro (symprod_wf_aux
        x_t
        (match acc_a with
         | AccIntro f -> f x_t p_a)
        y
        acc_b)
    | Right_sym _ _ _ _ ->
      let rec aux (y:b) (acc_b:acc b r_b y) (t:a & b) (p_t:sym_t r_a r_b t (x, y))
        : Tot (acc (a & b) (sym_t r_a r_b) t)
              (decreases acc_b)
        = match p_t with
         | Left_sym x_t _ _ p_a ->
           AccIntro (symprod_wf_aux
             x_t
             (match acc_a with
              | AccIntro f -> f x_t p_a)
             y
             acc_b)
         | Right_sym _ y_t _ p_b ->
           AccIntro (aux
             y_t
             (match acc_b with
              | AccIntro f -> f y_t p_b)) in
      aux y acc_b t p_t

let symprod_wf (#a #b:Type)
  (r_a:a -> a -> Type)
  (r_b:b -> b -> Type)
  (wf_a:well_founded a r_a)
  (wf_b:well_founded b r_b)
  : well_founded (a & b) (sym_t r_a r_b)
  = fun t -> AccIntro (symprod_wf_aux (fst t) (wf_a (fst t)) (snd t) (wf_b (snd t)))

