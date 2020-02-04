module MPar
assume
val s : Type0

let action a = s -> a & s

noeq
type m : Type -> Type =
 | Return : #a:Type -> x:a -> m a
 | Act : #a:Type -> #b:Type -> act:action a -> k:(a -> m b) -> m b
 | Par : #a0:Type -> #a1:Type -> #a:Type -> left:m a0 -> right:m a1 -> k:(a0 & a1 -> m a) -> m a

let tape = nat -> bool
let par a = tape & nat & s -> a & nat & s
let return #a (x:a) : par a = fun (t, n, s) -> x, n, s
let bind #a #b (f:par a) (g: a -> par b) : par b =
    fun (t, n, s) ->
      let a, n, s = f (t, n, s) in
      g a (t, n, s)
let rand : par bool = fun (t, n, s) -> t n, n+1, s
let get : par s = fun (t, n, s) -> s, n, s
let put s : par unit  = fun (t, n, _) -> (), n, s

let rec step #a (p:m a) : par (m a) =
  match p with
  | Return x ->
    return p

  | Act act k ->
    s0 <-- get ;
    let x, s1 = act s0 in
    put s1 ;;
    return (k x)

  | Par (Return x) (Return y) k ->
    FStar.WellFounded.axiom1 k (x, y);
    step (k (x, y))

  | Par l r k ->
    b <-- rand;
    if b
    then (l' <-- step l; return (Par l' r k))
    else (r' <-- step r; return (Par l r' k))

[@(expect_failure [19])]
let rec run #a (p:m a) : par a =
  p <-- step p ;
  match p with
  | Return x -> return x
  | _ -> run p

////////////////////////////////////////////////////////////////////////////////
