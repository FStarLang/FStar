module SymmetricTransitiveClosure

module L = FStar.List.Tot

(* Generalities on relations *)

type rel (a:Type) = a -> a -> Type0

let included_in (#a:Type) (r_1 r_2 : rel a) = forall (x y : a). r_1 x y ==> r_2 x y
let transitive (#a:Type) (r:rel a) = forall (x y z:a). r x y /\ r y z ==> r x z
let symmetric (#a:Type) (r:rel a) = forall (x y: a). r x y ==> r y x

(* Symmetric transitive closure of a relation *)

private
type triple (a:Type) = bool * a * a

private
let concat_pred (#a:Type) (r:rel a) ((rev, z1, z2): triple a) (z2':a) =
  if rev then r z2 z1 /\ z2 == z2' else r z1 z2 /\ z2 == z2'

private
let accumulate_path (#a:Type) (r:rel a) ((rev, z1, z2):triple a) (p, z2') =
  let pz1z2 = concat_pred #a r (rev, z1, z2) z2' in
  (pz1z2 /\ p), z1

private
let symmetric_transitive_closure (#a:Type) (r:rel a) : rel a =
  fun (x y:a) ->
    l:list (triple a){
      Cons? l /\
      (let (_, x',_) :: _ = l in x' == x) /\
      fst (L.fold_right (accumulate_path #a r) l (True, y))
    }

abstract
let stc (#a:Type) (r:rel a) : rel a = symmetric_transitive_closure #a r

abstract
let stc_inject (#a:Type) (r:rel a) (x y:a) : Pure (stc #a r x y) (requires (r x y)) (ensures (fun _ -> True)) =
  [false,x,y]

(* TODO : we want to be able to write something like [wxy @ wyz by induction wxy] *)
abstract
let rec transitivity (#a:Type) (r:rel a) (#x #y #z : a) (wxy:stc #a r x y) (wyz:stc #a r y z)
  : Tot (stc #a r x z) (decreases wxy)
=
  match wxy with
  | [b, x_0, x_1] -> (b, x_0, x_1) :: wyz
  | x_0 :: x_1 :: xs -> let (_, x', _) = x_1 in x_0 :: transitivity #a r #x' #y #z (x_1 :: xs) wyz

private
let rec symmetry' (#a:Type) (r:rel a) (x y z : a) (wyx:stc #a r y x) (wyz:stc #a r y z)
  : Tot (stc #a r x z) (decreases wyx)
=
  match wyx with
  | [b, x_0, x_1] -> let t = not b, x_1, x_0 in t :: wyz
  | (b_0, x_00, x_01) :: (b_1, x_10, x_11) :: xs -> symmetry' #a r x x_10 z ((b_1, x_10, x_11) :: xs) ((not b_0, x_01, x_00) :: wyz)

let symmetry (#a:Type) (r:rel a) (#x #y : a) (wxy:stc #a r x y) : stc #a r y x =
  match wxy with
  | [b, x, y] -> [not b, y, x]
  | (b, x, z) :: wzy -> symmetry' #a r y z x wzy [not b, z, x]

open FStar.Squash

private
let rec universal_property'
  (a:Type)
  (r p : rel a)
  (h:squash (r `included_in` p /\ transitive p /\ symmetric p))
  (x y : a)
  (w:stc r x y)
  : Lemma (requires True) (ensures (p x y)) (decreases w)
=
  match w with
  | [b, x_0, x_1] -> give_proof h ; assert (p x_0 x_1)
  | (b, x_0, x_1) :: ys ->
    let (_, x', _) :: _ = ys in
    universal_property' a r p h x' y ys ;
    give_proof h ;
    assert (p x_0 x_1) ;
    assert (p x' y) ;
    assert (x == x_0 /\ x_1 == x') ;
    assert (p x y)

open FStar.Classical

abstract
let universal_property (#a:Type) (r p : rel a)
  : Lemma (requires (r `included_in` p /\ transitive p /\ symmetric p))
    (ensures (stc r `included_in` p))
=
  let h = get_proof (r `included_in` p /\ transitive p /\ symmetric p) in
  forall_intro_2
    (fun x y -> impl_intro (universal_property' a r p h x y) <: Lemma (stc r x y ==> p x y))
