module Pure
open FStar.Mul

//SNIPPET_START: factorial$
let rec factorial (x:int)
  : Pure int (requires x >= 0) (ensures fun r -> r >= 1)
  = if x = 0
    then 1
    else x * factorial (x - 1)
//SNIPPET_END: factorial$

//SNIPPET_START: fact$
let fact (x:nat) : pos = factorial x
//SNIPPET_END: fact$

//SNIPPET_START: wp$
let pre = Type0
let post (a:Type) = a -> Type0
let wp (a:Type) = post a -> pre
//SNIPPET_END: wp$

//SNIPPET_START: return_wp$
let return_wp (#a:Type) (x:a) : wp a = fun post -> post x
//SNIPPET_END: return_wp$

//SNIPPET_START: bind_wp$
let bind_wp (#a #b:Type) (wp1:wp a) (wp2:a -> wp b)
  : wp b
  = fun post -> wp1 (fun x -> wp2 x post)                
//SNIPPET_END: bind_wp$

//SNIPPET_START: if_then_else_wp$
let if_then_else_wp (#a:Type) (b:bool) (wp1 wp2:wp a)
  : wp a
  = fun post -> if b then wp1 post else wp2 post
//SNIPPET_END: if_then_else_wp$


//SNIPPET_START: tot$
let tot (a:Type) = a
let return_tot (#a:Type) (x:a) : tot a = x
let bind_tot (#a #b:Type) (x:tot a) (y:a -> tot b)
  : tot b
  = let v = x in y v
//SNIPPET_END: tot$

//SNIPPET_START: mwp_laws$
(* A monotonic WP maps stronger postconditions to stronger preconditions *)
let monotonic (#a:Type) (wp:wp a) =
  forall (p q:post a). (forall x. p x ==> q x) ==> (wp p ==> wp q)

let mwp (a:Type) = w:wp a { monotonic w }

(* An equivalence relation on WPs *)
let ( =~= ) (#a:Type) (wp1 wp2:wp a)
  : prop
  = forall post. wp1 post <==> wp2 post

(* The three monad laws *)
let left_identity (a b:Type) (x:a) (wp:a -> mwp a)
  : Lemma (bind_wp (return_wp x) wp =~= wp x)
  = ()

let right_identity (a b:Type) (wp:mwp a)
  : Lemma (wp =~= (bind_wp wp return_wp))
  = ()

let associativity (a b c:Type) (wp1:mwp a) (wp2:a -> mwp b) (wp3:b -> mwp c)
  : Lemma (bind_wp wp1 (fun x -> bind_wp (wp2 x) wp3) =~=
           bind_wp (bind_wp wp1 wp2) wp3)
  = ()
//SNIPPET_END: mwp_laws$

open FStar.Mul

open FStar.Monotonic.Pure

//SNIPPET_START: square$
let square (n:int) 
  : PURE nat (as_pure_wp #nat (fun q -> n*n >= 0 /\ q (n * n)))
  = n * n
//SNIPPET_END: square$

//SNIPPET_START: stronger_wp$
let stronger_wp (#a:Type) (wp1 wp2:wp a) : prop =
   forall post. wp1 post ==> wp2 post
//SNIPPET_END: stronger_wp$

//SNIPPET_START: maybe_incr$
let maybe_incr (b:bool) (x:int)
  : PURE int (as_pure_wp (if_then_else_wp b
                                        (bind_wp (return_wp (x + 1)) (fun y -> return_wp y))
                                        (return_wp x)))
  = if b
    then let y = x + 1 in y
    else x
//SNIPPET_END: maybe_incr$


//SNIPPET_START: maybe_incr2$
let maybe_incr2 (b:bool) (x:int)
  : PURE int (as_pure_wp (fun post -> forall (y:int). y >= x ==> post y))
  = if b
    then let y = x + 1 in y
    else x
//SNIPPET_END: maybe_incr2$


//SNIPPET_START: maybe_incr_tot$
let maybe_incr_tot (b:bool) (x:int)
  : Tot (y:int { y >= x })
  = if b
    then let y = x + 1 in y
    else x
//SNIPPET_END: maybe_incr_tot$

//SNIPPET_START: assert_wp$
let assert_wp (#a:Type) (w:wp a) (p: a -> Type0) 
  : wp (x:a{ p x })
  = fun post -> w (fun (x:a) -> p x /\ post x)
//SNIPPET_END: assert_wp$


//SNIPPET_START: cont$
let cont (r:Type) (a:Type) = (a -> r) -> r  // (a -> r) is the continuation
let return #r (#a:Type) (x:a) : cont r a = fun k -> k x
let bind #r (#a #b:Type) (f:cont r a) (g:a -> cont r b)
  : cont r b
  =  fun k -> f (fun x -> g x k)
//SNIPPET_END: cont$
