module TypeclassesAlt2
open FStar.Ghost
let no_method = ()

class bounded_unsigned_int (a:Type) = {
   bound      : a;
   as_nat     : a -> nat;
   from_nat   : (x:nat { x <= as_nat bound }) -> a;
   [@@@no_method]
   bui_properties : squash (
     (forall (x:a). as_nat x <= as_nat bound) /\
     (forall (x:a). from_nat (as_nat x) == x) /\
     (forall (x:nat{ x <= as_nat bound}). as_nat (from_nat x) == x)
   )
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
  
let bound_subtraction_ok #a {| bounded_unsigned_int a |}
  = forall x. fits #a op_Subtraction bound x

class bounded_unsigned_int_ops (a:Type) = {
   [@@@no_method]
   base       : bounded_unsigned_int a;
   add        : (x:a -> y:a { fits ( + ) x y } -> a);
   sub        : (x:a -> y:a { fits op_Subtraction x y } -> a);
   comp       : (a -> a -> bool);
   properties : squash (
     related_ops ( + ) add /\
     related_ops op_Subtraction sub /\      
     bound_subtraction_ok #a /\
     (forall (x y:a). comp x y <==> as_nat x < as_nat y)     
   )
}

instance ops_base {| d : bounded_unsigned_int_ops 'a |} 
  : bounded_unsigned_int 'a 
  = d.base

let ( +^ ) {| bounded_unsigned_int_ops 'a |}
           (x : 'a)
           (y : 'a { fits ( + ) x y })
  : 'a
  = add x y

let ( -^ ) {| bounded_unsigned_int_ops 'a |}
           (x : 'a)
           (y : 'a { fits op_Subtraction x y })
  : 'a
  = sub x y

let ( <^ ) {| bounded_unsigned_int_ops 'a |}
           (x : 'a)
           (y : 'a)
  : bool
  = comp x y

class eq (a:Type) = {
  eq_op: a -> a -> bool;

  [@@@no_method]
  eq_properties : squash (
    forall x y. eq_op x y <==> x == y
  )
}

let ( = ) {| eq 'a |} (x y: 'a) = eq_op x y

instance bounded_unsigned_int_ops_eq {| bounded_unsigned_int_ops 'a |}
  : eq 'a
  = {
      eq_op = (fun x y -> not (x <^ y) && not (y <^ x));
      eq_properties = ()
    }

let ( <= ) {| bounded_unsigned_int_ops 'a |} (x y : 'a)
  : bool
  = x <^ y || x = y

instance u32_instance_base : bounded_unsigned_int FStar.UInt32.t =
  let open FStar.UInt32 in
  {
    bound    = 0xfffffffful;
    as_nat   = v;
    from_nat = uint_to_t;
    bui_properties = ()
}

instance u32_instance_ops : bounded_unsigned_int_ops FStar.UInt32.t =
  let open FStar.UInt32 in
  {
    base = u32_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    comp = (fun x y -> x <^ y);
    properties = ()
  }


instance u64_instance_base : bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    bound    = 0xffffffffffffffffuL;
    as_nat   = v;
    from_nat = uint_to_t;
    bui_properties = ()
}

instance u64_instance_ops : bounded_unsigned_int_ops FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    base = u64_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    comp = (fun x y -> x <^ y);
    properties = ()
  }

module U32 = FStar.UInt32
module U64 = FStar.UInt64

let test32 (x:U32.t)
           (y:U32.t)
  = if x <= 0xffffffful &&
       y <= 0xffffffful
    then Some (x +^ y)
    else None

let test64 (x y:U64.t)
  = if x <= 0xfffffffuL &&
       y <= 0xfffffffuL
    then Some (x +^ y)
    else None

module L = FStar.List.Tot

let try_add (x:U32.t)
            (y:U32.t)
  = if x <= (bound -^ y)
    then x +^ y
    else y

#push-options "--query_stats"
let sum {| bounded_unsigned_int_ops 'a |}
        (l:list 'a) (acc:'a)
  = 
  L.fold_right
    (fun (x:'a) (acc:option 'a) ->
      match acc with
      | None -> None
      | Some y ->
        if x <= (bound -^ y)
        then Some (x +^ y)
        else None)
    l
    (Some acc)


let testsum32 = sum [0x01ul; 0x02ul; 0x03ul] 0x00ul
let testsum64 = sum [0x01uL; 0x02uL; 0x03uL] 0x00uL
