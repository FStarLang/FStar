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

unfold
let related_ops #a {| bounded_unsigned_int a |}
                (iop: int -> int -> int)
                (bop: (x:a -> y:a { fits iop x y } -> a))
  = forall (x y:a).  fits iop x y ==> as_nat (bop x y) = as_nat x `iop` as_nat y
  
class addable_bounded_unsigned_int (a:Type) = {
   [@@@no_method]
   base_add      : bounded_unsigned_int a;
   add        : (x:a -> y:a { fits ( + ) x y } -> a);
   add_properties : squash (
     related_ops ( + ) add
   )
}

instance addable_base {| d : addable_bounded_unsigned_int 'a |} 
  : bounded_unsigned_int 'a 
  = d.base_add

let ( +^ ) {| addable_bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { fits ( + ) x y })
  : 'a
  = add x y

let bound_subtraction_ok #a {| bounded_unsigned_int a |}
  = forall x. fits #a op_Subtraction bound x

class subtractable_bounded_unsigned_int (a:Type) = {
   [@@@no_method]
   base_sub   : bounded_unsigned_int a;
   sub        : (x:a -> y:a { fits op_Subtraction x y } -> a);

   [@@@no_method]
   sub_properties : squash (
     related_ops op_Subtraction sub /\
     bound_subtraction_ok #a #base_sub
   )
}

instance subtractable_base {| d : subtractable_bounded_unsigned_int 'a |} 
  : bounded_unsigned_int 'a 
  = d.base_sub

let ( -^ ) {| subtractable_bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { fits( op_Subtraction ) x y })
  : 'a
  = sub x y

class comparable_bounded_unsigned_int (a:Type) = {
   [@@@no_method]
   base_comp   : bounded_unsigned_int a;
   comp        : a -> a -> bool;

   [@@@no_method]
   comp_properties : squash (
     (forall (x y:a).{:pattern comp x y} comp x y <==> as_nat x < as_nat y)
   )
}

instance comparable_base {| d : comparable_bounded_unsigned_int 'a |} 
  : bounded_unsigned_int 'a 
  = d.base_comp

let ( <^ ) {| comparable_bounded_unsigned_int 'a |}
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

instance comparable_bounded_unsigned_int_eq {| comparable_bounded_unsigned_int 'a |}
  : eq 'a
  = {
      eq_op = (fun x y -> not (x <^ y) && not (y <^ x));
      eq_properties = ()
    }

let ( <= ) {| comparable_bounded_unsigned_int 'a |} (x y : 'a)
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

instance u32_instance_add : addable_bounded_unsigned_int FStar.UInt32.t =
  let open FStar.UInt32 in
  {
    base_add = u32_instance_base;
    add      = (fun x y -> add x y);
    add_properties = ()
  }

instance u32_instance_sub : subtractable_bounded_unsigned_int FStar.UInt32.t =
  let open FStar.UInt32 in
  {
    base_sub = u32_instance_base;
    sub      = (fun x y -> sub x y);
    sub_properties = ()
  }

instance u32_instance_cmp : comparable_bounded_unsigned_int FStar.UInt32.t =
  let open FStar.UInt32 in
  {
    base_comp = u32_instance_base;
    comp    = (fun x y -> x <^ y);
    comp_properties = ()
  }


instance u64_instance_base : bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    bound    = 0xffffffffffffffffuL;
    as_nat   = v;
    from_nat = uint_to_t;
    bui_properties = ()
}

instance u64_instance_add : addable_bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    base_add = u64_instance_base;
    add      = (fun x y -> add x y);
    add_properties = ()
  }

instance u64_instance_sub : subtractable_bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    base_sub = u64_instance_base;
    sub      = (fun x y -> sub x y);
    sub_properties = ()
  }

instance u64_instance_cmp : comparable_bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    base_comp = u64_instance_base;
    comp    = (fun x y -> x <^ y);
    comp_properties = ()
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

#push-options "--query_stats --fuel 0 --ifuel 1"

[@@expect_failure [19]]
let try_sub {| bounded_unsigned_int 'a |}
            {| subtractable_bounded_unsigned_int 'a |}
            (acc:'a)
  = bound -^ acc

let try_sub {| b: bounded_unsigned_int 'a |}
            {| s: subtractable_bounded_unsigned_int 'a |}
            (acc:'a { s.base_sub == b } )
  = bound -^ acc

let try_sub' {| b: bounded_unsigned_int 'a |}
             {| s: subtractable_bounded_unsigned_int 'a |}
             (acc:'a)
  = bound #_ #s.base_sub -^ acc

let try_sub2 {| c: comparable_bounded_unsigned_int 'a |}
             {| s: subtractable_bounded_unsigned_int 'a |}
             (acc:'a { c.base_comp == s.base_sub })
  = bound -^ acc

let sum {| c : comparable_bounded_unsigned_int 'a |}
        {| a : addable_bounded_unsigned_int 'a |}
        {| s : subtractable_bounded_unsigned_int 'a |}
        (l:list 'a) (acc:'a { c.base_comp == a.base_add /\ a.base_add == s.base_sub })
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

class bounded_unsigned_int_ops (a:Type) = {
  _base_add: addable_bounded_unsigned_int a;
  _base_sub: subtractable_bounded_unsigned_int a;
  _base_comp: comparable_bounded_unsigned_int a;
}

instance _base #a {| d : bounded_unsigned_int_ops a |}
  : bounded_unsigned_int a 
  = d._base_sub.base_sub

instance __base_add #a {| d : bounded_unsigned_int_ops a |}
  : addable_bounded_unsigned_int a 
  = d._base_add

instance __base_sub #a {| d : bounded_unsigned_int_ops a |}
  : subtractable_bounded_unsigned_int a
  = d._base_sub

instance __base_comp #a {| d : bounded_unsigned_int_ops a |}
  : comparable_bounded_unsigned_int a 
  = d._base_comp

let try_sub3 {| bounded_unsigned_int_ops 'a |}
             (acc:'a)
  = bound -^ acc

  // L.fold_right
  //   (fun (x:'a) (acc:option 'a) ->
  //     match acc with
  //     | None -> None
  //     | Some y ->
  //       Some (bound -^ y)
  //       // if x <= (bound -^ y)
  //       // then Some (x +^ y)
  //       // else None
  // )
  //   l
  //   (Some acc)
