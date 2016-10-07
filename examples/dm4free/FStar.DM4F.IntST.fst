module FStar.DM4F.IntST

// Note: being in the [FStar] namespace, only [Prims] is automatically opened
// for the current module.

let st (a: Type) =
  int -> M (a * int)

val return_st : a:Type -> x:a -> st a
let return_st a x = fun s -> x, s

val bind_st : a:Type -> b:Type -> f:st a -> g:(a -> st b) -> st b
let bind_st a b f g = fun s0 ->
  let tmp = f s0 in
  let x, s1 = tmp in
  g x s1

let get (_:unit): st int =
  fun x -> x, x

let put x: st unit =
  fun _ -> (), x

reifiable reflectable new_effect_for_free {
  STINT: a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
  and effect_actions
       get      = get
     ; put      = put
}

let post = STINT.post
let pre = STINT.pre
let wp = STINT.wp

inline let lift_pure_stint (a:Type) (wp:pure_wp a) (n:int) (p:post a) = wp (fun a -> p (a, n))
sub_effect PURE ~> STINT = lift_pure_stint

effect StInt (a:Type) (pre: pre) (post: (int -> a -> int -> GTot Type0)) =
       STINT a (fun n0 p -> pre n0 /\ (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

effect St (a:Type) =
       STINT a (fun n0 p -> forall x. p x)

let repr = STINT.repr

//Although we have STINT.get and STINT.put now as actions, 
//we can also "rederive" them using reflection

// From the definition language to the effectful world with WPs
val action_get: (u:unit) -> repr int (fun n post -> post (n, n))
let action_get () i = (i, i)

val action_put: x:int -> repr unit (fun n post -> post ((), x))
let action_put x i = ((), x)

reifiable val get' : unit -> STINT int (fun z post -> post (z, z))
let get' () = STINT.reflect (action_get ())

reifiable val put': x:int -> STINT unit (fun z post -> post ((), x))
let put' x = STINT.reflect (action_put x)


val incr : unit -> StInt unit (requires (fun n -> True))
                             (ensures (fun n0 _ n1 -> n1 = n0 + 1))
let incr u =
  let n = STINT.get () in
  STINT.put (n + 1)

val incr' : unit -> STINT unit
  (fun s0 post -> forall (s1:int). (s1 > s0) ==> post ((), s1))
let incr' u =
  let n = STINT.get () in
  STINT.put (n + 1)

reifiable val incr2 : unit -> St unit 
let incr2 u =
    let n = STINT.get() in
    STINT.put (n + 1)

let assert_after_reify (_:unit) : St unit =
    let n0 = STINT.get() in
    let _, n1 = reify (incr2 ()) n0 in
    assert (n1 = n0 + 1);
    STINT.put n1

val assert_after_reflect : unit -> St int
let assert_after_reflect u =
    let n0 = STINT.get () in
    STINT.reflect (action_put (n0 + 2));
    let n1 = STINT.get () in
    assert (n0 + 2 = n1);
    n1

val reflect_on_the_fly : unit -> St int
let reflect_on_the_fly u =
    let n0 = STINT.get () in
    let add_two : repr unit (fun n post -> post ((), n + 2)) = //need this annotation, since reflect doesn't insert a M.return; but it should
      fun n0 -> (), n0+2 in
    STINT.reflect add_two;
    let n1 = STINT.get () in
    assert (n0 + 2 = n1);
    n1
