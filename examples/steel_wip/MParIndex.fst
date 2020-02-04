module MParIndex
assume
val s : Type0

let action a = s -> a & s

noeq
type m : nat -> Type -> Type =
 | Return : #a:Type -> x:a -> m 0 a
 | Act : #a:Type -> #b:Type -> #n:nat -> act:action a -> k:(a -> m n b) -> m (n + 1) b
 | Par : #a0:Type -> #a1:Type -> #a:Type -> #n0:_ -> #n1:_ -> #n:_ -> left:m n0 a0 -> right:m n1 a1 -> k:(a0 & a1 -> m n a) -> m (n0 + n1 + n + 1) a

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

let nm a = n:nat & m n a

let ( <? ) #a #b (x:nm a) (y:nm b) =
  let (| n, p  |) = x in
  let (| n', _ |) = y in 
  n < n' \/ Return? p

let reduct #a (redex:nm a) = x:nm a { x <? redex}


let rec step #a (redex:nm a)
  : Tot (par (reduct redex))
        (decreases (dsnd redex))
  = let ret = return #(reduct redex) in
    match dsnd redex with
    | Return x ->
      return redex

    | Act act k ->
      s0 <-- get ;
      let x, s1 = act s0 in
      put s1 ;;
      ret (| _, k x |)

    | Par (Return x) (Return y) k ->
      ret (| _ ,  k (x, y) |)

    | Par l r k ->
      b <-- rand;
      if (b || Return? r) && not (Return? l)
      then (l' <-- step (| _, l |); 
            let (| nl', l' |) = l' in
            ret (| _, Par l' r k |))
      else (r' <-- step (| _, r |); 
            let (| nr', r' |) = r' in
            ret (| _, Par l r' k |))


let rec run #a (redex:nm a) 
  : Tot (par a) 
        (decreases (dfst redex))
  = p <-- step redex ;
    match dsnd p with
    | Return x -> return x
    | _ -> run p

