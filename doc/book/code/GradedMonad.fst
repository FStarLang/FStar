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
class graded_monad (#index:Type)
                   (m: monoid index -> index -> Type -> Type) = 
{
  return : #a:Type -> #im:monoid index -> x:a -> m im one a;
  
  bind   : #a:Type -> #b:Type -> #ia:index -> #ib:index -> #im:monoid index ->
           m im ia a -> 
           (a -> m im ib b) ->
           m im (op ia ib) b

}
//SNIPPET_END: graded_monad$

//we now have do notation for graded monads

//SNIPPET_START: counting$
let count_st (s:Type) (_:monoid nat) (count:nat) (a:Type) = s -> a & s & z:nat{z==count}

let count_return (#s:Type) (#a:Type) (#im:monoid nat) (x:a) : count_st s im one a = fun s -> x, s, one #nat

let count_bind (#s:Type) (#a:Type) (#b:Type) (#ia:nat) (#ib:nat) (#im:monoid nat)
               (f:count_st s im ia a)
               (g:(a -> count_st s im ib b))
  : count_st s im (op ia ib) b
  = fun s -> let x, s, n = f s in
          let y, s', m = g x s in
          y, s', op #nat n m

instance count_st_graded (s:Type) : graded_monad #nat (count_st s) =
{ 
  return = count_return #s;
  bind = count_bind #s;
}

// A write-counting grade monad
let get #s : count_st s monoid_nat_plus 0 s = fun s -> s, s, 0
let put #s (x:s) : count_st s monoid_nat_plus 1 unit = fun _ -> (), x, 1
//SNIPPET_END: counting$

//SNIPPET_START: test$
let test #s =
  x <-- get #s ;
  put x

//F* + SMT automatically proves that the index simplifies to 2
let test2 #s : count_st s monoid_nat_plus 2 unit =
  x <-- get #s;
  put x;;
  put x
//SNIPPET_END: test$
