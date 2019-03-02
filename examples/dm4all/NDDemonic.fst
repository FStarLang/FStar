module NDDemonic

module List = FStar.List.Tot

let repr (a:Type) = list a

let return (a:Type u#a) (x:a) = [x]

let bind (a : Type u#aa) (b : Type u#bb)
    (l : repr a) (f : a -> repr b) = List.flatten (List.map f l)

(* Demonic interpretation *)
let interp (#a:Type) (l : repr a) : pure_wp a =
    fun p -> forall (x:a). List.memP x l ==> p x

total
reifiable
reflectable
new_effect {
  ND : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = pure_wp
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     ; interp    = interp
}

assume val test_f : unit -> ND int (fun p -> p 5 /\ p 3)
let l : (l:list int{forall p. p 5 /\ p 3 ==> interp l p}) = reify (test_f ())

effect Nd (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ND a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

val choose : #a:Type0 -> x:a -> y:a -> ND a (fun p -> p x /\ p y)
let choose #a x y =
    ND?.reflect [x;y]

val fail : #a:Type0 -> unit -> ND a (fun p -> True)
let fail #a () =
    ND?.reflect []

let flip () : ND bool (fun p -> p true /\ p false) =
    choose true false

let test () : ND int (fun p -> forall (x:int). 0 <= x /\ x < 10 ==> p x) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

[@expect_failure]
let test_bad () : ND int (fun p -> forall (x:int). 0 <= x /\ x < 5 ==> p x) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

let rec pick_from #a (l : list a) : ND a (fun p -> forall x. List.memP x l ==> p x) =
    match l with
    | [] -> fail ()
    | x::xs ->
      if flip ()
      then x
      else pick_from xs

let guard (b:bool) : ND unit (fun p -> b ==> p ()) =
  if b
  then ()
  else fail ()

let ( * ) = op_Multiply

let pyths () : ND (int & int & int) (fun p -> forall x y z. x*x + y*y == z*z ==> p (x,y,z)) =
  let l = [1;2;3;4;5;6;7;8;9;10] in
  let x = pick_from l in
  let y = pick_from l in
  let z = pick_from l in
  guard (x*x + y*y = z*z);
  (x,y,z)

(* Extracted code for pyths:

let (pyths_norm : unit -> (Prims.int * Prims.int * Prims.int) Prims.list) =
  fun uu____1038  ->
    [((Prims.parse_int "3"), (Prims.parse_int "4"), (Prims.parse_int "5"));
    ((Prims.parse_int "4"), (Prims.parse_int "3"), (Prims.parse_int "5"));
    ((Prims.parse_int "6"), (Prims.parse_int "8"), (Prims.parse_int "10"));
    ((Prims.parse_int "8"), (Prims.parse_int "6"), (Prims.parse_int "10"))]
*)
let pyths_norm () = normalize_term (reify (pyths ()))
