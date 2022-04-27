module Typeclasses
module TC = FStar.Tactics.Typeclasses

//SNIPPET_START: printable$
class printable (a:Type) =
{
  to_string : a -> string
}
//SNIPPET_END: printable$

//SNIPPET_START: printable_bool_and_int$
instance printable_bool : printable bool =
{
  to_string = Prims.string_of_bool
}

instance printable_int : printable int =
{
  to_string = Prims.string_of_int
}
//SNIPPET_END: printable_bool_and_int$

//SNIPPET_START: printb and printi$
let printb (x:bool) = to_string x
let printi (x:int) = to_string x
//SNIPPET_END: printb and printi$

//SNIPPET_START: printable_list$
instance printable_list (#a:Type) (x:printable a) : printable (list a) =
{
  to_string = (fun l -> "[" ^ FStar.String.concat "; " (List.Tot.map to_string l) ^ "]")
}
//SNIPPET_END: printable_list$

//SNIPPET_START: printis and printbs$
let printis (l:list int) = to_string l
let printbs (l:list bool) = to_string l
//SNIPPET_END: printis and printbs$

//SNIPPET_START: print_any_list_explicit$
let print_any_list_explicit #a ( _ : printable a ) (l:list a) = to_string l
let _ = print_any_list_explicit printable_int [1;2;3]
//SNIPPET_END: print_any_list_explicit$

//SNIPPET_START: print_any_list$
let print_any_list #a {| _ : printable a |} (l:list a) = to_string l
let _ex1 = print_any_list [[1;2;3]]
let _ex2 = print_any_list #_ #(printable_list printable_int) [[1;2;3]]
//SNIPPET_END: print_any_list$

//SNIPPET_START: print_any_list_alt$
let print_any_list_alt #a {| printable a |} (l:list a) = to_string l
//SNIPPET_END: print_any_list_alt$

//SNIPPET_START: print_answer$
instance printable_string : printable string =
{
  to_string = fun x -> "\"" ^ x ^ "\""
}

instance printable_pair #a #b {| printable a |} {| printable b |} : printable (a & b) =
{
  to_string = (fun (x, y) -> "(" ^ to_string x ^ ", " ^ to_string y ^ ")")
}

instance printable_option #a #b {| printable a |} : printable (option a) =
{
  to_string = (function None -> "None" | Some x -> "(Some " ^ to_string x ^ ")")
}

instance printable_either #a #b {| printable a |} {| printable b |} : printable (either a b) =
{
  to_string = (function Inl x -> "(Inl " ^ to_string x ^ ")" | Inr x -> "(Inr " ^ to_string x ^ ")")
}

let _ = to_string [Inl (0, 1); Inr (Inl (Some true)); Inr (Inr "hello") ]

//You can always pass the typeclass instance you want explicitly, if you really want to
//typeclass resolution really saves you from LOT of typing!
let _ = to_string #_
             #(printable_list
                (printable_either #_ #_ #(printable_pair #_ #_ #printable_int #printable_int)
                                        #(printable_either #_ #_ #(printable_option #_ #printable_bool)
                                                                 #(printable_string))))
             [Inl (0, 1); Inr (Inl (Some true)); Inr (Inr "hello")]
//SNIPPET_END: print_answer$

//SNIPPET_START: bounded_unsigned_int$
class bounded_unsigned_int (a:Type) = {
   bound      : a;
   as_nat     : a -> nat;
   from_nat   : (x:nat { x <= as_nat bound }) -> a;
   fits       : (op: (int -> int -> int) -> a -> a -> prop);
   add        : (x:a -> y:a { fits ( + ) x y } -> a);
   sub        : (x:a -> y:a { fits ( op_Subtraction ) x y } -> a);
   lt         : (a -> a -> bool);

   [@@@TC.no_method]
   properties : squash (
     (forall (x y:a) (op: int -> int -> int). fits op x y <==>
                0 <= op (as_nat x) (as_nat y) /\
                op (as_nat x) (as_nat y) <= as_nat bound) /\
     (forall (x y:a). fits ( + ) x y ==> as_nat (add x y) = as_nat x + as_nat y) /\
     (forall (x y:a). fits ( op_Subtraction ) x y ==> as_nat (sub x y) = as_nat x - as_nat y) /\
     (forall (x:a). fits ( op_Subtraction ) bound x) /\
     (forall (x:a). as_nat x <= as_nat bound) /\
     (forall (x:a). from_nat (as_nat x) == x) /\
     (forall (x:nat{ x <= as_nat bound}). as_nat (from_nat x) == x) /\
     (forall (x y:a). lt x y <==> as_nat x < as_nat y)
   )
}
//SNIPPET_END: bounded_unsigned_int$

let ( +^ ) {| bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { fits ( + ) x y })
  : 'a
  = add x y

let ( -^ ) {| bounded_unsigned_int 'a |}
           (x : 'a)
           (y : 'a { fits ( op_Subtraction ) x y })
  : 'a
  = sub x y

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
    fits     = (fun op x y -> let res = op (v x) (v y) in
                           0 <= res /\ res <= FStar.UInt.max_int 32);
    add      = (fun x y -> add x y);
    sub      = (fun x y -> sub x y);
    lt       = ( <^ );
    properties = ()
}


instance u64_instance : bounded_unsigned_int FStar.UInt64.t =
  let open FStar.UInt64 in
  {
    bound    = 0xffffffffffffffffuL;
    as_nat   = v;
    from_nat = uint_to_t;
    fits     = (fun op x y -> let res = op (v x) (v y) in
                           0 <= res /\ res <= FStar.UInt.max_int 64);
    add      = (fun x y -> add x y);
    sub      = (fun x y -> sub x y);
    lt       = ( <^ );
    properties = ()
}


//SNIPPET_START: eq$
class eq (a:Type) = {
  eq_op: a -> a -> bool;

  [@@@TC.no_method]
  properties : squash (
    forall x y. eq_op x y <==> x == y
  )
}
//SNIPPET_END: eq$

let ( =?= ) {| eq 'a |} (x y: 'a) = eq_op x y


instance bounded_unsigned_int_eq {| bounded_unsigned_int 'a |}
  : eq 'a
  = {
      eq_op = (fun x y -> not (lt x y) && not (lt y x));
      properties = ()
    }

let ( <= ) {| bounded_unsigned_int 'a |} (x y : 'a)
  : bool
  = x <^ y || x =?= y

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
