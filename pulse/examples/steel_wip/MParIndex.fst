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


// let tape = nat -> bool
// let par a = tape & nat & s -> a & nat & s
// let return #a (x:a) : par a = fun (t, n, s) -> x, n, s
// let bind #a #b (f:par a) (g: a -> par b) : par b =
//     fun (t, n, s) ->
//       let a, n, s = f (t, n, s) in
//       g a (t, n, s)
// let rand : par bool = fun (t, n, s) -> t n, n+1, s
// let get : par s = fun (t, n, s) -> s, n, s
// let put s : par unit  = fun (t, n, _) -> (), n, s

let nm a = n:nat & m n a

let ( <? ) #a #b (x:nm a) (y:nm b) =
  let (| n, p  |) = x in
  let (| n', _ |) = y in 
  n < n' \/ Return? p

let reduct #a (redex:nm a) = x:nm a { x <? redex}

let step_ret (#a:Type u#a) (redex:nm a{Return? (dsnd redex)})
: Eff (reduct redex)
= redex

// let step_act (#a:Type u#a) (redex:nm a{Act? (dsnd redex)})
// : Eff (reduct redex)
// = let node = dsnd redex in
//   let (act, k) = Act?.act node, Act?.k node in  //AR: TODO: FIXME: match act with | ... doesn' work

// #restart-solver
#set-options "--log_queries --fuel 4 --ifuel 4 --debug MParIndex --debug_level LayeredEffects --debug_level Extreme --print_implicits --ugly"
let rec step (#a:Type u#a) (redex:nm a)
  : Eff (reduct #a redex)
        //(decreases (dsnd redex))
  = //let ret = returnc #(reduct #a redex) in\
    let node = dsnd redex in

    match node with
    | Act act k ->
      let s0 = get () in
      let x, s1 = act s0 in
      put s1;
      (| _, k x |)
    | _ -> admit ()


    // | Act _ _ -> step_act redex


    // | _ -> admit ()


    //   s0 <-- get ;
    //   let x, s1 = act s0 in
    //   put s1 ;;
    //   ret (| _, k x |)

    // | Par (Return x) (Return y) k ->
    //   ret (| _ ,  k (x, y) |)

    // | Par l r k ->
    //   b <-- rand;
    //   if (b || Return? r) && not (Return? l)
    //   then (l' <-- step (| _, l |); 
    //         let (| nl', l' |) = l' in
    //         ret (| _, Par l' r k |))
    //   else (r' <-- step (| _, r |); 
    //         let (| nr', r' |) = r' in
    //         ret (| _, Par l r' k |))


// let rec run #a (redex:nm a) 
//   : Tot (par a) 
//         (decreases (dfst redex))
//   = p <-- step redex ;
//     match dsnd p with
//     | Return x -> return x
//     | _ -> run p

