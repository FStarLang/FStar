module Bug3659

let point t = unit -> t
let dv_point t = unit -> Dv t

let cast (#t: Type u#a) (f: point t) : dv_point t = f

let is_inj #t #s (f: t->s) : prop =
  forall x y. f x == f y ==> x == y

// The `cast` function must not be injective.
[@@expect_failure [19]]
let cast_inj_fails (t: Type u#a) : squash (is_inj (cast #t)) = ()

// Otherwise we would get an unsoundness:
let cast_inj (t: Type u#a) : squash (is_inj (cast #t)) = admit ()

let to_type (#t: Type0) (x: t) : Type0 = y:t { y == x }
let to_type_inj t : squash (is_inj (to_type #t)) =
  introduce forall (x y: t). to_type x == to_type y ==> x == y with
  introduce _ ==> _ with _.
  let x: to_type x = x in
  let x: to_type y = coerce_eq () x in
  ()

let const #t (x: t) : point t = fun _ -> x
let const_inj t : squash (is_inj (const #t)) =
  assert forall x. const #t x () == x

let f (t: Type u#a) : GTot Type0 = to_type (cast (const t))
let f_inj : squash (Functions.is_inj (f u#a)) =
  to_type_inj (dv_point (Type u#a));
  cast_inj (Type u#a);
  const_inj (Type u#a)

let contradiction : squash False =
  Cardinality.Universes.no_inj_universes_suc f
