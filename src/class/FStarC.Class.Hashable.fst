module FStarC.Class.Hashable

open FStar open FStarC
open FStarC
open FStarC.Hash
open FStarC.Class.Show
open FStarC.Class.Deq
open FStarC.Class.Ord

instance showable_hash_code : showable hash_code = {
  show = string_of_hash_code;
}

instance eq_hash_code : deq hash_code = {
  ( =? ) = (=);
}

instance ord_hash_code : ord hash_code = {
  super = FStar.Tactics.Typeclasses.solve;
  cmp = (fun x y -> Order.order_from_int (cmp_hash x y));
}

instance hashable_int    : hashable int = { hash = of_int; }
instance hashable_string : hashable string = { hash = of_string; }
instance hashable_bool   : hashable bool = {
  hash = (fun b -> if b then of_int 1 else of_int 2);
}

instance hashable_list
  (_ : hashable 'a)
: Tot (hashable (list 'a)) = {
  hash = (fun xs -> List.fold_left (fun h x -> mix h (hash x)) (of_int 0) xs);
}

instance hashable_option
  (_ : hashable 'a)
: Tot (hashable (option 'a)) = {
  hash = (fun x -> match x with None -> of_int 0 | Some x -> mix (of_int 1) (hash x));
}

instance hashable_either
  (_ : hashable 'a)
  (_ : hashable 'b)
: Tot (hashable (either 'a 'b)) = {
  hash = (fun x -> match x with Inl a -> mix (of_int 0) (hash a) | Inr b -> mix (of_int 1) (hash b));
}

instance hashable_tuple2
  (_ : hashable 'a)
  (_ : hashable 'b)
: Tot (hashable ('a & 'b)) = {
  hash = (fun (a, b) -> hash a `mix` hash b);
}

instance hashable_tuple3
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
: Tot (hashable ('a & 'b & 'c)) = {
  hash = (fun (a, b, c) -> hash a `mix` hash b `mix` hash c);
}

instance hashable_tuple4
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
  (_ : hashable 'd)
: Tot (hashable ('a & 'b & 'c & 'd)) = {
  hash = (fun (a, b, c, d) -> hash a `mix` hash b `mix` hash c `mix` hash d);
}

instance hashable_tuple5
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
  (_ : hashable 'd)
  (_ : hashable 'e)
: Tot (hashable ('a & 'b & 'c & 'd & 'e)) = {
  hash = (fun (a, b, c, d, e) -> hash a `mix` hash b `mix` hash c `mix` hash d `mix` hash e);
}

instance hashable_tuple6
  (_ : hashable 'a)
  (_ : hashable 'b)
  (_ : hashable 'c)
  (_ : hashable 'd)
  (_ : hashable 'e)
  (_ : hashable 'f)
: Tot (hashable ('a & 'b & 'c & 'd & 'e & 'f)) = {
  hash = (fun (a, b, c, d, e, f) -> hash a `mix` hash b `mix` hash c `mix` hash d `mix` hash e `mix` hash f);
}
