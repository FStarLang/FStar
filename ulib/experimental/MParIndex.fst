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
 | Act : #a:Type u#a -> action a -> m 1 a
 | Par : #a0:Type u#a -> #a1:Type u#a ->
          #n0:_ -> #n1:_ ->
          left:m n0 a0 -> right:m n1 a1 -> m (n0 + n1 + 1) (a0 & a1)
 | Bind : #a:_ -> #b:_ -> #n1:_ -> #n2:_ ->
          f:m n1 a -> g:(x:a -> m n2 b) -> m (n1 + n2 + 1) b

let nm a = n:nat & m n a

let ( <? ) #a #b ((| n, p |) : nm a) ((| n', _ |) :nm b) =
  n < n' \/ Return? p

let reduct #a (redex:nm a) = x:nm a { x <? redex}

let rec step (#a:Type u#a) (redex:nm a)
  : Eff (nm a)
        (decreases (dfst redex))
  = match dsnd redex with
    | Return _ -> redex
    | Act act ->
      let s0 = get () in
      let x, s1 = act s0 in
      put s1;
      (| _, Return x |)

    | Bind (Return x) k -> (| _, k x |)

    | Bind m k -> let (| _, m' |) = step (| _,  m |) in (| _, Bind m' k |)

    | Par (Return x) (Return y) ->
      (| _, Return (x, y) |)

    | Par l (Return y) ->
      let (| _, l' |) = step (| _, l |) in
      (| _, Par l' (Return y) |)

    | Par (Return x) r ->
      let (| _, r' |) = step (| _, r |) in
      (| _, Par (Return x) r' |)

    | Par l r ->
      if sample () then
        let (| _, l' |) = step (| _, l |) in
        (| _, Par l' r |)
      else
        let (| _, r' |) = step (| _, r |) in
        (| _, Par l r' |)

let rec step_redex (#a:Type u#a) (redex:nm a)
  : Eff (reduct redex)
        (decreases (dfst redex))
  = match dsnd redex with
    | Return _ -> redex
    | Act act ->
      let s0 = get () in
      let x, s1 = act s0 in
      put s1;
      (| _, Return x |)
    | Par #a0 #a1 #_ #_ (Return x) (Return y) ->
      (| 0, Return #(a0 & a1) (x, y) |)
    | Par l (Return y) ->
      let (| _, l' |) = step_redex (| _, l |) in
      (| _, Par l' (Return y) |)

    | Par (Return x) r ->
      let (| _, r' |) = step_redex (| _, r |) in
      (| _, Par (Return x) r' |)
    | Par l r ->
      let b = sample () in
      if b then
        let (| _, l' |) = step_redex (| _, l |) in
        (| _, Par l' r |)
      else
        let (| _, r' |) = step_redex (| _, r |) in
        (| _, Par l r' |)

     | Bind #_ #b #_ #n2 (Return x) g -> (| n2, (g x <: m n2 b) |)

     | Bind f g ->
       let (| _, f' |) = step_redex (| _, f |) in
       (| _, Bind f' g |)

let rec run #a (p:nm a) : Eff (nm a) (decreases (dfst p)) =
  match dsnd p with
  | Return _ -> p
  | _ ->
    let p = step_redex p in run p
