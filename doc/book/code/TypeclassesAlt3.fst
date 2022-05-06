module TypeclassesAlt3
module TC = FStar.Tactics.Typeclasses

//SNIPPET_START: bounded_unsigned_int$
class bounded_unsigned_int (a:Type) = {
   bound      : a;
   as_nat     : a -> nat;
   from_nat   : (x:nat { x <= as_nat bound }) -> a;
   [@@@FStar.Tactics.Typeclasses.no_method]
   properties : squash (
     (forall (x:a). as_nat x <= as_nat bound) /\ // the bound is really an upper bound
     (forall (x:a). from_nat (as_nat x) == x) /\ //from_nat/as_nat form a bijection
     (forall (x:nat{ x <= as_nat bound}). as_nat (from_nat x) == x)
   )
}
//SNIPPET_END: bounded_unsigned_int$

//SNIPPET_START: fits$
let fits #a {| bounded_unsigned_int a |}
            (op: int -> int -> int)
            (x y:a)
  : prop
  = 0 <= op (as_nat x) (as_nat y) /\
    op (as_nat x) (as_nat y) <= as_nat #a bound
//SNIPPET_END: fits$

//SNIPPET_START: related_ops$
let related_ops #a {| bounded_unsigned_int a |}
                (iop: int -> int -> int)
                (bop: (x:a -> y:a { fits iop x y } -> a))
  = forall (x y:a).  fits iop x y ==> as_nat (bop x y) = as_nat x `iop` as_nat y
//SNIPPET_END: related_ops$  

//SNIPPET_START: bui_ops$
class bounded_unsigned_int_ops (a:Type) = {
   [@@@TC.no_method]
   base       : bounded_unsigned_int a;
   add        : (x:a -> y:a { fits ( + ) x y } -> a);
   sub        : (x:a -> y:a { fits op_Subtraction x y } -> a);
   lt         : (a -> a -> bool);
   [@@@TC.no_method]
   properties : squash (
     related_ops ( + ) add /\
     related_ops op_Subtraction sub /\      
     (forall (x y:a). lt x y <==> as_nat x < as_nat y) /\ // lt is related to <
     (forall (x:a). fits op_Subtraction bound x) //subtracting from the maximum element never triggers underflow
   )
}
//SNIPPET_END: bui_ops$

//SNIPPET_START: ops_base$
instance ops_base #a {| d : bounded_unsigned_int_ops a |} 
  : bounded_unsigned_int a
  = d.base
//SNIPPET_END: ops_base$

//SNIPPET_START: ops$
let ( +^ ) #a {| bounded_unsigned_int_ops a |}
           (x : a)
           (y : a { fits ( + ) x y })
  : a
  = add x y

let ( -^ ) #a {| bounded_unsigned_int_ops a |}
           (x : a)
           (y : a { fits op_Subtraction x y })
  : a
  = sub x y

let ( <^ ) #a {| bounded_unsigned_int_ops a |}
           (x : a)
           (y : a)
  : bool
  = lt x y
//SNIPPET_END: ops$

//SNIPPET_START: eq$
class eq (a:Type) = {
  eq_op: a -> a -> bool;

  [@@@TC.no_method]
  properties : squash (
    forall x y. eq_op x y <==> x == y
  )
}

let ( =?= ) #a {| eq a |} (x y: a) = eq_op x y
//SNIPPET_END: eq$

//SNIPPET_START: bui_eq$
instance bounded_unsigned_int_ops_eq #a {| bounded_unsigned_int_ops a |}
  : eq a
  = {
      eq_op = (fun x y -> not (x <^ y) && not (y <^ x));
      properties = ()
    }

let ( <=^ ) #a {| bounded_unsigned_int_ops a |} (x y : a)
  : bool
  = x <^ y || x =?= y
//SNIPPET_END: bui_eq$

//SNIPPET_START: ground_instances$
module U32 = FStar.UInt32
module U64 = FStar.UInt64
instance u32_instance_base : bounded_unsigned_int U32.t =
  let open U32 in
  {
    bound    = 0xfffffffful;
    as_nat   = v;
    from_nat = uint_to_t;
    properties = ()
}

instance u32_instance_ops : bounded_unsigned_int_ops U32.t =
  let open U32 in
  {
    base = u32_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    lt   = (fun x y -> lt x y);
    properties = ()
  }


instance u64_instance_base : bounded_unsigned_int U64.t =
  let open U64 in
  {
    bound    = 0xffffffffffffffffuL;
    as_nat   = v;
    from_nat = uint_to_t;
    properties = ()
}

instance u64_instance_ops : bounded_unsigned_int_ops U64.t =
  let open U64 in
  {
    base = u64_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    lt   = (fun x y -> lt x y);
    properties = ()
  }
//SNIPPET_END: ground_instances$

//SNIPPET_START: ground_tests$
let test32 (x:U32.t)
           (y:U32.t)
  = if x <=^ 0xffffffful &&
       y <=^ 0xffffffful
    then Some (x +^ y)
    else None

let test64 (x y:U64.t)
  = if x <=^ 0xfffffffuL &&
       y <=^ 0xfffffffuL
    then Some (x +^ y)
    else None
//SNIPPET_END: ground_tests$

//SNIPPET_START: sum$
module L = FStar.List.Tot
let sum #a {| bounded_unsigned_int_ops a |}
        (l:list a) (acc:a)
  : option a 
  = L.fold_right
     (fun (x:a) (acc:option a) ->
       match acc with
       | None -> None
       | Some y ->
         if x <=^ bound -^ y
         then Some (x +^ y)
         else None)
     l
     (Some acc)

let testsum32 : U32.t = Some?.v (sum [0x01ul; 0x02ul; 0x03ul] 0x00ul)
let testsum64 : U64.t = Some?.v (sum [0x01uL; 0x02uL; 0x03uL] 0x00uL)
//SNIPPET_END: sum$

//SNIPPET_START: testsum32'$
let testsum32' : U32.t =
  let x = sum #U32.t [0x01ul; 0x02ul; 0x03ul;0x01ul; 0x02ul; 0x03ul;0x01ul; 0x02ul; 0x03ul] 0x00ul in
  assert_norm (Some? x /\ as_nat (Some?.v x) == 18);
  Some?.v x
//SNIPPET_END: testsum32'$
