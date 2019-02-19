module NDAngelic

module List = FStar.List.Tot

let repr (a:Type) = list a

let return (a:Type u#a) (x:a) = [x]

let bind (a : Type u#aa) (b : Type u#bb)
    (l : repr a) (f : a -> repr b) = List.flatten (List.map f l)

(* let choose (#a : Type) (x y : a) : repr a = [x;y] *)

(* Angelic interpretation *)
let interp (a:Type) (l : repr a) : pure_wp a =
    fun p -> exists (x:a). List.memP x l /\ p x

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

     (* ; choose    = choose *)
}

let test1 () : ND int (fun p -> p 5 /\ p 3) = 5
let test2 () : ND int (fun p -> p 5 /\ p 3) = 3

// Whoa! This used to succeed since the effect is marked as reifiable,
// and Rel compares the representation types on each side for the
// subtyping. and both are just `unit -> list a`. I changed it to check
// the WPs via stronger-than instead of always unfolding.
[@expect_failure]
let test3 () : ND int (fun p -> p 5 /\ p 3) = 4

effect Nd (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ND a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect NDTot (a:Type) = ND a (pure_null_wp a)

val choose : #a:Type0 -> x:a -> y:a -> ND a (fun p -> p x \/ p y)
let choose #a x y =
    ND?.reflect [x;y]

val fail : #a:Type0 -> unit -> ND a (fun p -> False)
let fail #a () =
    ND?.reflect []

let test () : ND int (fun p -> exists (x:int). 6 <= x /\ x <= 9 /\ p x) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

[@expect_failure]
let test_bad () : ND int (fun p -> exists (x:int). 0 <= x /\ x < 5 /\ p x) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

let rec pick #a (l : list a) : ND a (fun p -> exists x. List.memP x l /\ p x) =
    match l with
    | [] -> fail ()
    | x::xs ->
      // choose x (pick xs)
      // ^ this is wrong! it will call `pick xs` before choosing and always
      //   end up returning []
      if choose true false
      then x
      else pick xs

let gguard (b:bool) : ND unit (fun p -> b /\ p ()) =
  if b
  then ()
  else fail ()

let ( * ) = op_Multiply

open FStar.Tactics

(* This takes a while ... *)
#push-options "--z3rlimit 100"
let pyths () : ND (int & int & int) (fun p -> exists x y z. x >= 1 /\ x <= 10 /\
                                                            y >= 1 /\ y <= 10 /\
                                                            z >= 1 /\ z <= 10 /\
                                                            x*x + y*y == z*z /\
                                                            p (x,y,z))
               by (compute (); explode ())
             =
  let l = [1;2;3;4;5;6;7;8;9;10] in
  let x = pick l in
  let y = pick l in
  let z = pick l in
  gguard (x*x + y*y = z*z);
  (x,y,z)
#pop-options

(* Check ND.ml for the triples:

let (pyths_norm : unit -> (Prims.int * Prims.int * Prims.int) Prims.list) =
  fun uu____1038  ->
    [((Prims.parse_int "3"), (Prims.parse_int "4"), (Prims.parse_int "5"));
    ((Prims.parse_int "4"), (Prims.parse_int "3"), (Prims.parse_int "5"));
    ((Prims.parse_int "6"), (Prims.parse_int "8"), (Prims.parse_int "10"));
    ((Prims.parse_int "8"), (Prims.parse_int "6"), (Prims.parse_int "10"))]
*)
let pyths_norm () = normalize_term (reify (pyths ()))

let test_reify_1 () = assert (reify (test1 ()) ==  [5])
let test_reify_2 () = assert (reify (test2 ()) ==  [3])
let test_reify_3 () = assert (reify (test1 ()) =!= [4])

[@expect_failure]
let _ = assert False
