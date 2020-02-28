module MParIndex

assume val state : Type0

type tape = nat -> bool

type repr (a:Type) (_:unit) =
  (tape & nat & state) -> PURE (a & nat & state) (fun p -> forall x. p x)

let return (a:Type) (x:a)
: repr a ()
= fun (t, n, s) -> (x, n, s)

let bind (a:Type) (b:Type)
  (f:repr a ()) (g:a -> repr b ())
: repr b ()
= fun (t, n, s) ->
  let x, n, s = f (t, n, s) in
  (g x) (t, n, s)

let subcomp (a:Type)
  (f:repr a ())
: repr a ()
= f

let if_then_else (a:Type)
  (f:repr a ())
  (g:repr a ())
  (p:Type0)
: Type
= repr a ()

total reifiable reflectable
layered_effect {
  EFF : a:Type -> unit -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let lift_pure_eff (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: Pure (repr a ())
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)
= fun (t, n, s) -> f (), n, s

sub_effect PURE ~> EFF = lift_pure_eff

effect Eff (a:Type) = EFF a ()

let get () : Eff state
= EFF?.reflect (fun (_, n, s) -> s, n, s)

let put (s:state) : Eff unit
= EFF?.reflect (fun (_, n, _) -> (), n, s)

let sample () : Eff bool
= EFF?.reflect (fun (t, n, s) -> t n, n+1, s)

let action a = state -> a & state

noeq
type m : nat -> Type u#a -> Type =
 | Return : #a:Type u#a -> x:a -> m 0 a
 | Act : #a:Type u#a -> #b:Type u#a -> #n:nat -> act:action a -> k:(a -> m n b) -> m (n + 1) b
 | Par : #a0:Type u#a -> #a1:Type u#a -> #a:Type u#a -> #n0:_ -> #n1:_ -> #n:_ -> left:m n0 a0 -> right:m n1 a1 -> k:(a0 & a1 -> m n a) -> m (n0 + n1 + n + 1) a

let nm a = n:nat & m n a

let ( <? ) #a #b (x:nm a) (y:nm b) =
  let (| n, p  |) = x in
  let (| n', _ |) = y in 
  n < n' \/ Return? p

let reduct #a (redex:nm a) = x:nm a { x <? redex}

let rec step (#a:Type u#a) (redex:nm a)
  : Eff (reduct redex)
        (decreases (dsnd redex))
  = match dsnd redex with
    | Return _ -> redex
    | Act act k ->
      let s0 = get () in
      let x, s1 = act s0 in
      put s1;
      (| _, k x |)

    | Par #_ #_ #_ #_ #_ #n (Return x) (Return y) k ->
      (| n, k (x, y) |)

    | Par l r k ->
      let b = sample () in
      if (b || Return? r) && not (Return? l)
      then
        let (| _, l' |) = step (| _, l|) in
        (| _, Par l' r k |)
      else
        let (| _, r' |) = step (| _, r |) in
        (| _, Par l r' k |)
