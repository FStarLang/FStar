module TCUnivs

(* This caused a very hard to find failure in the normalizer due to
pushing un-evaluated universe arguments on the stack. It is a
shrunk down version of TypeclassesAlt3 from the book, but I'm keeping
a copy here just in case. -- Guido 2023/11/03 *)

module TC = FStar.Tactics.Typeclasses

class bounded_unsigned_int (a:Type) = {
   bound      : a;
   as_nat     : a -> nat;
   from_nat   : (x:nat { x <= as_nat bound }) -> a;
}

let fits #a {| bounded_unsigned_int a |}
            (op: int -> int -> int)
            (x y:a)
  : prop
  = 0 <= op (as_nat x) (as_nat y) /\
    op (as_nat x) (as_nat y) <= as_nat #a bound

let related_ops #a {| bounded_unsigned_int a |}
                (iop: int -> int -> int)
                (bop: (x:a -> y:a { fits iop x y } -> a))
  = forall (x y:a).  fits iop x y ==> as_nat (bop x y) = as_nat x `iop` as_nat y

class bounded_unsigned_int_ops (a:Type) = {
   base       : bounded_unsigned_int a;
   add        : (x:a -> y:a { fits ( + ) x y } -> a);
   sub        : (x:a -> y:a { fits op_Subtraction x y } -> a);
   lt         : (a -> a -> bool);
}

instance ops_base #a {| d : bounded_unsigned_int_ops a |}
  : bounded_unsigned_int a
  = d.base

let ( <=^ ) #a {| bounded_unsigned_int_ops a |} (x y : a)
  : bool
  = true

module U32 = FStar.UInt32
instance u32_instance_base : bounded_unsigned_int U32.t =
  let open U32 in
  {
    bound    = 0xfffffffful;
    as_nat   = v;
    from_nat = uint_to_t;
}

instance u32_instance_ops : bounded_unsigned_int_ops U32.t =
  let open U32 in
  {
    base = u32_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    lt   = (fun x y -> lt x y);
  }

module L = FStar.List.Tot
let sum #a (d : bounded_unsigned_int_ops a )
        (l:list a) (acc:a)
  : option a
  = admit();
    L.fold_right
     (fun (x:a) (acc:option a) ->
       match acc with
       | None -> None
       | Some y ->
         if x <=^ bound `sub` y
         then Some (x `add` y)
         else None)
     l
     (Some acc)

let testsum32' : unit =
  let x = sum #U32.t u32_instance_ops [0x1ul] 0x00ul in
  assert_norm (Some? x)
