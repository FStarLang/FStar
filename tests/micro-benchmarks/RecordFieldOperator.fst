module RecordFieldOperator

// Operators are allowed as field name
noeq type foo = {
  ( ^ ): int -> int -> int;
}
let bar: foo = {
  ( ^ ) = (fun x y -> x + y + 1);
}

// Here, the field [^] is just desugared to [op_Hat]
let _ = assert_norm (bar.op_Hat 10 5 == 16)

// This is useful when opening a record...
let _ =
  let open bar <: foo in
  assert_norm (1 ^ 2 ^ 3 ^ 4 ^ 5 == 15 + 4)

// ...but especially useful working with typeclasses
class hasPlus 'a = { ( + ): 'a -> 'a -> 'a }

instance stringHasPlus: hasPlus string
  = { (+) = ( ^ ); }
instance intHasPlus: hasPlus int
  = { (+) = Prims.op_Addition; }

let _ =
  assert_norm (3 + 39 == 42);
  assert_norm ("3" + "39" == "339")

// or, even better:
class monad1 (m: Type -> Type) = {
  ( >>= ): #a:Type -> #b:Type -> m a -> (a -> m b) -> m b;
  ret1: #a:Type -> a -> m a
}

instance _: monad1 option = {
  ( >>= ) = (fun #a (x: option a) f -> match x with
                                  | Some x -> f x
                                  | None   -> None );
  ret1 = Some
}

let ex1 = Some 3 >>= (fun x -> Some (x+4))

// or with let operators:
class monad2 (m: Type -> Type) = {
  ( let* ): #a:Type -> #b:Type -> m a -> (a -> m b) -> m b;
  ret2: #a:Type -> a -> m a
}

instance monad2_from_1 (m1: monad1 't): monad2 't = {
  ( let* ) = ( >>= );
  ret2 = ret1
}

let ex2 =
  let* x = Some 3 in
  Some (x+4)
