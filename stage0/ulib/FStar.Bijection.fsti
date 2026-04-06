module FStar.Bijection

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

let ( =~ ) a b = bijection a b

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

private
let o f g = fun x -> f (g x)

let bij_comp (#a #b #c : Type) (ab : a =~ b) (bc : b =~ c) : (a =~ c) =
{
  right = bc.right `o` ab.right;
  left = ab.left `o` bc.left;
  right_left = (fun x -> ab.right_left (bc.left x); bc.right_left x);
  left_right = (fun x -> bc.left_right (ab.right x); ab.left_right x);
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
