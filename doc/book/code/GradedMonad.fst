module GradedMonad

//SNIPPET_START: monoid$
class monoid (a:Type) =
{
   op   : a -> a -> a;
   one  : a;
   properties: squash (
     (forall (x:a). op one x == x /\ op x one == x) /\
     (forall (x y z:a). op x (op y z) == op (op x y) z)
   );
}

instance monoid_nat_plus : monoid nat =
{
  op = (fun (x y:nat) -> x + y);
  one = 0;
  properties = ()
}
//SNIPPET_END: monoid$

//SNIPPET_START: graded_monad$
class graded_monad (#index:Type) {| monoid index |}
                   (m : index -> Type -> Type) = 
{
  return : #a:Type -> x:a -> m one a;
  
   ( let+ )   : #a:Type -> #b:Type -> #ia:index -> #ib:index ->
           m ia a -> 
           (a -> m ib b) ->
           m (op ia ib) b

}
//SNIPPET_END: graded_monad$

//we now have do notation for graded monads

//SNIPPET_START: counting$
let count_st (s:Type) (count:nat) (a:Type) = s -> a & s & z:nat{z==count}

let count_return (#s:Type) (#a:Type) (x:a) : count_st s one a = fun s -> x, s, one #nat

let count_bind (#s:Type) (#a:Type) (#b:Type) (#ia:nat) (#ib:nat)
               (f:count_st s ia a)
               (g:(a -> count_st s ib b))
  : count_st s (op ia ib) b
  = fun s -> let x, s, n = f s in
          let y, s', m = g x s in
          y, s', op #nat n m

instance count_st_graded (s:Type) : graded_monad (count_st s) =
{ 
  return = count_return #s;
  ( let+ ) = count_bind #s;
}

// A write-counting grade monad
let get #s : count_st s 0 s = fun s -> s, s, 0
let put #s (x:s) : count_st s 1 unit = fun _ -> (), x, 1
//SNIPPET_END: counting$

//SNIPPET_START: test$
let test #s =
  let+ x = get #s in
  put x

//F* + SMT automatically proves that the index simplifies to 2
let test2 #s : count_st s 2 unit =
  let+ x = get in
  put x ;+
  put x
//SNIPPET_END: test$
