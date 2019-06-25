module Bug1750


//This is a minimized version of the original bug report by Jay Bosamiya
let t_f = bool -> Tot bool
let t_g = bool -> GTot bool
[@(expect_failure [19])]
let test (b:bool) (f:'a{'a == t_f}) (g:'b{'b == t_g}) =
  if b then f else g

//This next test exercises the equivalnce of the HasType relation
//for functions types that differ only by currying
let t_t_f = bool -> t_f
//We expect the equality of `a == t_t_h` to suffice in showing
//via SMT that HasType x (bool -> bool -> bool -> bool)
//This is meant to work because:
// 1. t_t_f is encoded as
//       HasType f t_t_f <==>
//          (forall x. HasType x bool ==> HasType (f x) t_f) /\
//          IsTotFun f
// 2. t_f is encoded as
//       HasType f t_f <==>
//           (forall x. HasType x bool ==> HasType (f x) bool) /\
//           IsTotFun f
// 3. t_bbb = bool -> bool -> bool
//       HasType f t_bbb <==>
//            forall x y. HasType x bool /\ HasType y bool ==>
//                          HasType (f x y) bool /\
//            IsTotFun f /\
//            forall x. HasType x bool ==> IsTotFun (f x) <---****Typing guard?
//The crucial bit to see here is in the very last axiom
//In particular, why do we need the typing guard?
//If we want to prove (HasType f t_t_f ==> HasType f t_bbb)
//Then, without the typing guard, we need to prove that
//   forall x. IsTotFun (f x)          (Goal)
//But, from the encoding of t_t_f, we only get
//   forall x. HasType x bool ==> HasType (f x) t_f
//   ==> forall x. HasType x bool ==> IsTotFun (f x)
//Which isn't enough to prove (Goal)
//So, those typing guards, though they may seem unnecessary
//are actually needed
let test_currying #a (x:a{a == t_t_f}) : bool -> bool -> bool = x

//This is intentionally marked `rec` so that its SMT interpretation
//is guarded by typing hypotheses on its arguments
let rec apply (f:int -> int) (x:int) : int = f x
let plus (x y : int) = x + y

//This tests derivability of the has_type relation for partial
//applications of top-level functions
let test_partial_app0 (x y : int) = assert (apply (plus x) y == plus x y)

//This tests that partial app typing doesn't incorrectly introduce
//an unsoundness ... a previous version did!
[@(expect_failure [19])]
let test_partial_app1 (f:int -> int -> int) (g:int -> bool) (x y:int) : Lemma False =
  assert (apply (f x) y == f x y);
  assert (has_type (g x) int);
  assert (has_type (g x) bool)

//This tests derivability of the has_type relation for partial
//applications of function-typed bound variables
let test_partial_app2 (f:int -> int -> int) (x y:int) =
  assert (apply (f x) y == f x y)

//This tests derivability of the has_type relation for partial
//applications of function-typed bound variables
let ref_t = f:(int -> int -> int){forall x y. f x y > x}
let test_partial_app3 (f:ref_t) (x y:int) =
  assert (apply (f x) y == f x y)

//This is Jay's original bug report
type eff_tag =
  | G
  | T

let eff (t:eff_tag) (b:Type) =
  match t with
  | T -> unit -> Tot b
  | G -> unit -> GTot b

let eff_to_tot (x:eff T 'a) : Tot 'a = x ()

let gtot_to_eff #a #b (f:(x:a -> GTot (b x))) : x:a -> eff G (b x) = fun x () -> f x

assume val t : Type0

[@(expect_failure [19])]
let foo (#e:eff_tag) (x:Ghost.erased t) : eff e t = (gtot_to_eff #(Ghost.erased t) #(fun _ -> t) Ghost.reveal) x

val bug : #t:Type0 -> (x:Ghost.erased t) -> Tot (y:t{y == Ghost.reveal x})

[@(expect_failure [19])]
let bug #t x =
  let foo #e (x:Ghost.erased t) : eff e t = (gtot_to_eff Ghost.reveal) x in
  eff_to_tot (foo x)
