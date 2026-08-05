module FStar.Bijection

open FStar.Ghost
open FStar.Fin { fin }
open FStar.Injection
open FStar.Mul

(* total function composition *)
let o #a #b #c (g : b -> Tot c) (f : a -> Tot b) : a -> Tot c = fun x -> g (f x)

noeq
type bijection (a b : Type) = {
  (* Functions between the types, the name indicates
  the direction we're "moving" in *)
  right : a -> b;
  left  : b -> a;

  (* Proofs that the functions are inverses of each other. As
  usual the name here is a tough choice. We call the first one
  "right_left" because it says something about "right (left x)". *)
  left_right : x:a -> squash (left (right x) == x);
  right_left : y:b -> squash (right (left y) == y);
}

(* A symbol *)
let ( =~ ) a b = bijection a b

val bij_inv_fwd (#a #b : _) (d : a =~ b) (x:a)
  : Lemma (x == d.left (d.right x))
          [SMTPat (d.right x)]

val bij_inv_bk (#a #b : _) (d : a =~ b) (y:b)
  : Lemma (y == d.right (d.left y))
          [SMTPat (d.left y)]

(* Sometimes useful to specify implicits. See #3804. *)
let mk_bijection
  (#a #b : _)
  (right : a -> b)
  (left  : b -> a)
  (right_left : (x:b -> squash (right (left x) == x)))
  (left_right : (x:a -> squash (left (right x) == x)))
  : (a =~ b) =
  Mkbijection right left left_right right_left

(* Move values across bijections. *)
let ( >> ) (#a #b : Type) (x : a) (bij : a =~ b) : b = bij.right x
let ( << ) (#a #b : Type) (x : b) (bij : a =~ b) : a = bij.left x

val inv_lemma_pat (#a #b : _) (d : a =~ b) (x:a) (y:b)
  : Lemma ((x >> d) == y <==> x == (y << d))
          [SMTPat (d.right x); SMTPat (d.left y)]

let bij_self (a:Type) : (a =~ a) =
{
  right = id;
  left = id;
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

let bij_sym (#a #b : Type) (d : a =~ b) : (b =~ a) =
{
  right = d.left;
  left = d.right;
  right_left = d.left_right;
  left_right = d.right_left;
}

let bij_comp (#a #b #c : Type) (ab : a =~ b) (bc : b =~ c) : (a =~ c) =
{
  right = bc.right `o` ab.right;
  left = ab.left `o` bc.left;
  right_left = (fun x -> ab.right_left (bc.left x); bc.right_left x);
  left_right = (fun x -> bc.left_right (ab.right x); ab.left_right x);
}

let bij_erase (#a #b : Type) (bij : a =~ b) : (erased a =~ erased b) =
{
  right = (fun (x : erased a) -> bij.right x <: erased b);
  left = (fun (x : erased b) -> bij.left x <: erased a);
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}


let bij_flip_prod (#a #b : Type) : (a & b =~ b & a) =
{
  right = (fun (x, y) -> (y, x));
  left = (fun (y, x) -> (x, y));
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

let bij_prod (#a #b #c #d : Type) (ab : a =~ b) (cd : c =~ d) : (a & c =~ b & d) =
{
  right = (fun (x, y) -> (ab.right x, cd.right y));
  left = (fun (x, y) -> (ab.left x, cd.left y));
  right_left = (fun x ->
    let (x1, x2) = x in
    ab.right_left x1; cd.right_left x2);
  left_right = (fun x ->
    let (x1, x2) = x in
    ab.left_right x1; cd.left_right x2);
}

let bij_either (#a #b #c #d : Type)
  (ab : a =~ b) (cd : c =~ d) : (either a c =~ either b d) =
{
  right = (fun x -> match x with
    | Inl x -> Inl (ab.right x)
    | Inr y -> Inr (cd.right y));
  left = (fun x -> match x with
    | Inl x -> Inl (ab.left x)
    | Inr y -> Inr (cd.left y));
  left_right = (fun _ -> ());
  right_left = (fun _ -> ());
}

let bij_flip_sum (#a #b : Type) : (either a b =~ either b a) =
{
  right = (function | Inl x -> Inr x | Inr y -> Inl y);
  left = (function | Inl x -> Inr x | Inr y -> Inl y);
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

let bij_unit_fin1 : bijection unit (fin 1) = {
  right = (fun _ -> 0 <: fin 1);
  left = (fun _ -> ());
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(* weird typing errors without hoisting. *)
unfold
inline_for_extraction noextract
let prod_right (n1 n2 : nat) : fin n1 & fin n2 -> fin (n1 * n2) =
  // fun (x, y) -> (x * n2 + y)
  fun xy -> (xy._1 * n2 + xy._2)

unfold
inline_for_extraction noextract
let prod_left (n1 n2 : nat) : fin (n1 * n2) -> fin n1 & fin n2 =
  fun i -> (i / n2, i % n2)

unfold
let bij_nat_prod (#n1 #n2 : nat) : (fin n1 & fin n2 =~ fin (n1 * n2)) =
{
  right = prod_right n1 n2;
  left = prod_left n1 n2;
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

val __bij_cardinal (n1 n2 : nat) (bij : fin n1 =~ fin n2)
  : Lemma (n1 == n2)

val bij_cardinal (n1 n2 : nat)
  : Lemma (requires exists (b : fin n1 =~ fin n2). True)
          (ensures n1 == n2)

let bij_nat_sum (n1 n2 : nat)
  : (either (fin n1) (fin n2) =~ fin (n1 + n2)) =
{
  right = (fun (x : either (fin n1) (fin n2)) ->
    (match x with
     | Inl i -> i
     | Inr j -> n1 + j) <: fin (n1 + n2));
  left = (fun (i : fin (n1 + n2)) ->
    if i < n1
    then Inl i
    else Inr (i - n1));
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}


(***** Injections from bijections *****)

let inj_bij (#a #b : Type) (bij : a =~ b) : (a @~> b) =
  {
    f = bij.right;
    is_inj = (fun _ _ _ -> ());
  }

let inj_bij' (#a #b : Type) (bij : a =~ b) : (b @~> a) =
  {
    f = bij.left;
    is_inj = (fun _ _ _ -> ());
  }
