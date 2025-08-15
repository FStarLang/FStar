open Fstarcompiler
open Prims
type ('a, 'b) bijection =
  {
  right: 'a -> 'b ;
  left: 'b -> 'a ;
  left_right: unit ;
  right_left: unit }
let __proj__Mkbijection__item__right : 'a 'b . ('a, 'b) bijection -> 'a -> 'b
  =
  fun projectee ->
    match projectee with | { right; left; left_right; right_left;_} -> right
let __proj__Mkbijection__item__left : 'a 'b . ('a, 'b) bijection -> 'b -> 'a
  =
  fun projectee ->
    match projectee with | { right; left; left_right; right_left;_} -> left
type ('a, 'b) op_Equals_Tilde = ('a, 'b) bijection
let mk_bijection :
  'a 'b .
    ('a -> 'b) -> ('b -> 'a) -> unit -> unit -> ('a, 'b) op_Equals_Tilde
  =
  fun right ->
    fun left ->
      fun right_left ->
        fun left_right -> { right; left; left_right = (); right_left = () }
let op_Greater_Greater : 'a 'b . 'a -> ('a, 'b) op_Equals_Tilde -> 'b =
  fun x -> fun bij -> bij.right x
let op_Less_Less : 'a 'b . 'b -> ('a, 'b) op_Equals_Tilde -> 'a =
  fun x -> fun bij -> bij.left x
let bij_self : 'a . unit -> ('a, 'a) op_Equals_Tilde =
  fun uu___ ->
    {
      right = (fun x -> x);
      left = (fun x -> x);
      left_right = ();
      right_left = ()
    }
let bij_sym : 'a 'b . ('a, 'b) op_Equals_Tilde -> ('b, 'a) op_Equals_Tilde =
  fun d ->
    { right = (d.left); left = (d.right); left_right = (); right_left = () }
let o :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu -> 'uuuuu1) -> ('uuuuu2 -> 'uuuuu) -> 'uuuuu2 -> 'uuuuu1
  = fun f -> fun g -> fun x -> f (g x)
let bij_comp :
  'a 'b 'c .
    ('a, 'b) op_Equals_Tilde ->
      ('b, 'c) op_Equals_Tilde -> ('a, 'c) op_Equals_Tilde
  =
  fun ab ->
    fun bc ->
      {
        right = (o bc.right ab.right);
        left = (o ab.left bc.left);
        left_right = ();
        right_left = ()
      }
let bij_flip_prod : 'a 'b . unit -> (('a * 'b), ('b * 'a)) op_Equals_Tilde =
  fun uu___ ->
    {
      right = (fun uu___1 -> match uu___1 with | (x, y) -> (y, x));
      left = (fun uu___1 -> match uu___1 with | (y, x) -> (x, y));
      left_right = ();
      right_left = ()
    }
let bij_prod :
  'a 'b 'c 'd .
    ('a, 'b) op_Equals_Tilde ->
      ('c, 'd) op_Equals_Tilde -> (('a * 'c), ('b * 'd)) op_Equals_Tilde
  =
  fun ab ->
    fun cd ->
      {
        right =
          (fun uu___ ->
             match uu___ with | (x, y) -> ((ab.right x), (cd.right y)));
        left =
          (fun uu___ ->
             match uu___ with | (x, y) -> ((ab.left x), (cd.left y)));
        left_right = ();
        right_left = ()
      }
let bij_either :
  'a 'b 'c 'd .
    ('a, 'b) op_Equals_Tilde ->
      ('c, 'd) op_Equals_Tilde ->
        (('a, 'c) Fstarcompiler.FStar_Pervasives.either,
          ('b, 'd) Fstarcompiler.FStar_Pervasives.either) op_Equals_Tilde
  =
  fun ab ->
    fun cd ->
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
let bij_flip_sum :
  'a 'b .
    unit ->
      (('a, 'b) Fstarcompiler.FStar_Pervasives.either,
        ('b, 'a) Fstarcompiler.FStar_Pervasives.either) op_Equals_Tilde
  =
  fun uu___ ->
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
