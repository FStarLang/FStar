open Fstarcompiler
open Prims
type ('a, 'b) bijection =
  {
  right: 'a -> 'b ;
  left: 'b -> 'a ;
  left_right: unit ;
  right_left: unit }
let __proj__Mkbijection__item__right (projectee : ('a, 'b) bijection) :
  'a -> 'b=
  match projectee with | { right; left; left_right; right_left;_} -> right
let __proj__Mkbijection__item__left (projectee : ('a, 'b) bijection) :
  'b -> 'a=
  match projectee with | { right; left; left_right; right_left;_} -> left
type ('a, 'b) op_Equals_Tilde = ('a, 'b) bijection
let mk_bijection (right : 'a -> 'b) (left : 'b -> 'a) (right_left : unit)
  (left_right : unit) : ('a, 'b) op_Equals_Tilde=
  { right; left; left_right = (); right_left = () }
let op_Greater_Greater (x : 'a) (bij : ('a, 'b) op_Equals_Tilde) : 'b=
  bij.right x
let op_Less_Less (x : 'b) (bij : ('a, 'b) op_Equals_Tilde) : 'a= bij.left x
let bij_self (uu___ : unit) : ('a, 'a) op_Equals_Tilde=
  {
    right = (fun x -> x);
    left = (fun x -> x);
    left_right = ();
    right_left = ()
  }
let bij_sym (d : ('a, 'b) op_Equals_Tilde) : ('b, 'a) op_Equals_Tilde=
  { right = (d.left); left = (d.right); left_right = (); right_left = () }
let o (f : 'uuuuu -> 'uuuuu1) (g : 'uuuuu2 -> 'uuuuu) (x : 'uuuuu2) :
  'uuuuu1= f (g x)
let bij_comp (ab : ('a, 'b) op_Equals_Tilde) (bc : ('b, 'c) op_Equals_Tilde)
  : ('a, 'c) op_Equals_Tilde=
  {
    right = (o bc.right ab.right);
    left = (o ab.left bc.left);
    left_right = ();
    right_left = ()
  }
let bij_flip_prod (uu___ : unit) : (('a * 'b), ('b * 'a)) op_Equals_Tilde=
  {
    right = (fun uu___1 -> match uu___1 with | (x, y) -> (y, x));
    left = (fun uu___1 -> match uu___1 with | (y, x) -> (x, y));
    left_right = ();
    right_left = ()
  }
let bij_prod (ab : ('a, 'b) op_Equals_Tilde) (cd : ('c, 'd) op_Equals_Tilde)
  : (('a * 'c), ('b * 'd)) op_Equals_Tilde=
  {
    right =
      (fun uu___ -> match uu___ with | (x, y) -> ((ab.right x), (cd.right y)));
    left =
      (fun uu___ -> match uu___ with | (x, y) -> ((ab.left x), (cd.left y)));
    left_right = ();
    right_left = ()
  }
let bij_either (ab : ('a, 'b) op_Equals_Tilde)
  (cd : ('c, 'd) op_Equals_Tilde) :
  (('a, 'c) Fstarcompiler.FStar_Pervasives.either,
    ('b, 'd) Fstarcompiler.FStar_Pervasives.either) op_Equals_Tilde=
  {
    right =
      (fun x ->
         match x with
         | Fstarcompiler.FStar_Pervasives.Inl x1 ->
             Fstarcompiler.FStar_Pervasives.Inl (ab.right x1)
         | Fstarcompiler.FStar_Pervasives.Inr y ->
             Fstarcompiler.FStar_Pervasives.Inr (cd.right y));
    left =
      (fun x ->
         match x with
         | Fstarcompiler.FStar_Pervasives.Inl x1 ->
             Fstarcompiler.FStar_Pervasives.Inl (ab.left x1)
         | Fstarcompiler.FStar_Pervasives.Inr y ->
             Fstarcompiler.FStar_Pervasives.Inr (cd.left y));
    left_right = ();
    right_left = ()
  }
let bij_flip_sum (uu___ : unit) :
  (('a, 'b) Fstarcompiler.FStar_Pervasives.either,
    ('b, 'a) Fstarcompiler.FStar_Pervasives.either) op_Equals_Tilde=
  {
    right =
      (fun uu___1 ->
         match uu___1 with
         | Fstarcompiler.FStar_Pervasives.Inl x ->
             Fstarcompiler.FStar_Pervasives.Inr x
         | Fstarcompiler.FStar_Pervasives.Inr y ->
             Fstarcompiler.FStar_Pervasives.Inl y);
    left =
      (fun uu___1 ->
         match uu___1 with
         | Fstarcompiler.FStar_Pervasives.Inl x ->
             Fstarcompiler.FStar_Pervasives.Inr x
         | Fstarcompiler.FStar_Pervasives.Inr y ->
             Fstarcompiler.FStar_Pervasives.Inl y);
    left_right = ();
    right_left = ()
  }
