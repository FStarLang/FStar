module TypeclassesAlt
open FStar.Ghost
let no_method = ()

let fits #a (bound:a)
            (as_nat: a -> nat)
            (from_nat: (x:nat { x <= as_nat bound } -> a))
            (op: int -> int -> int)
            (x y: a)
  : prop
  = 0 <= op (as_nat x) (as_nat y) /\
    op (as_nat x) (as_nat y) <= as_nat bound

class bounded_unsigned_int (a:Type) = {
   bound      : a;
   as_nat     : a -> nat;
   from_nat   : (x:nat { x <= as_nat bound }) -> a;
   add        : (x:a -> y:a { fits bound as_nat from_nat ( + ) x y } -> a);
   sub        : (x:a -> y:a { fits bound as_nat from_nat ( op_Subtraction ) x y } -> a);
   mul        : (x:a -> y:a { fits bound as_nat from_nat ( op_Multiply ) x y } -> a);
   lt         : (a -> a -> bool);

   [@@@no_method]
   bui_properties : squash (
     (forall (x y:a). fits bound as_nat from_nat ( + ) x y ==> as_nat (add x y) = as_nat x + as_nat y) /\
     (forall (x y:a). fits bound as_nat from_nat ( op_Subtraction ) x y ==> as_nat (sub x y) = as_nat x - as_nat y) /\
     (forall (x:a). fits bound as_nat from_nat ( op_Subtraction ) bound x) /\
     (forall (x y:a). fits bound as_nat from_nat ( op_Multiply ) x y ==> as_nat (mul x y) = as_nat x `op_Multiply` as_nat y) /\
     (forall (x:a). as_nat x <= as_nat bound) /\
     (forall (x:a). from_nat (as_nat x) == x) /\
     (forall (x:nat{ x <= as_nat bound}). as_nat (from_nat x) == x) /\
     (forall (x y:a). lt x y <==> as_nat x < as_nat y)
   )
}

let ok (#a:Type) {| bounded_unsigned_int a |} = fits #a bound as_nat from_nat

let ( +^ ) {| bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { ok ( + ) x y })
  : 'a
  = add x y

let ( -^ ) {| bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { ok ( op_Subtraction ) x y })
  : 'a
  = sub x y

let ( *^ ) {| bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { ok ( op_Multiply ) x y })
  : 'a
  = mul x y

let ( <^ ) {| bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a)
  : bool
  = lt x y

instance u32_instance : bounded_unsigned_int FStar.UInt32.t =
  let open FStar.UInt32 in
  {
    bound    = 0xfffffffful;
    as_nat   = v;
    from_nat = uint_to_t;
    add      = (fun x y -> add x y);
    sub      = (fun x y -> sub x y);
    mul      = (fun x y -> mul x y);
    lt       = ( <^ );
    bui_properties = ()
}


instance u64_instance : bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    bound    = 0xffffffffffffffffuL;
    as_nat   = v;
    from_nat = uint_to_t;
    add      = (fun x y -> add x y);
    sub      = (fun x y -> sub x y);
    mul      = (fun x y -> mul x y);
    lt       = ( <^ );
    bui_properties = ()
}

class eq (a:Type) = {
  eq_op: a -> a -> bool;

  [@@@no_method]
  eq_properties : squash (
    forall x y. eq_op x y <==> x == y
  )
}

let ( = ) {| eq 'a |} (x y: 'a) = eq_op x y

instance bounded_unsigned_int_eq {| bounded_unsigned_int 'a |}
  : eq 'a
  = {
      eq_op = (fun x y -> not (lt x y) && not (lt y x));
      eq_properties = ()
    }

let ( <= ) {| bounded_unsigned_int 'a |} (x y : 'a)
  : bool
  = x <^ y || x = y

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


let sum {| bounded_unsigned_int 'a |} (l:list 'a) (acc:'a)
  = L.fold_right
    (fun (x:'a) (acc:option 'a) ->
      match acc with
      | None -> None
      | Some y ->
        if x <= (bound -^ y)
        then Some (x +^ y)
        else None)
    l
    (Some acc)
