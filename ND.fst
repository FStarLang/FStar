module ND

module List = FStar.List.Tot

let wpty = pure_wp

let repr (a:Type) = unit -> list a
let repr' (a:Type) (_wp : wpty a) = unit -> list a

let return (a:Type u#a) (x:a) = fun () -> [x]

let bind (a : Type u#aa) (b : Type u#bb)
    (l : repr a) (f : a -> repr b) = fun () -> List.flatten (List.map (fun x -> f x ()) (l ()))

let choose (#a : Type) (x y : a) : repr a = fun () -> [x;y]

total
reifiable
reflectable
new_effect {
  ND : a:Type -> Effect
  with
       repr      = repr'
     ; return    = return
     ; bind      = bind

     ; wp_type   = wpty
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     (* ; choose    = choose *)
}

let test1 () : ND int (fun p -> p 5 /\ p 3) = 5
let test2 () : ND int (fun p -> p 5 /\ p 3) = 3

#set-options "--debug_level High,Rel"

// Whoa! This used to succeed since the effect is marked as reifiable,
// and Rel compares the representation types on each side for the
// subtyping. and both are just `unit -> list a`. I changed it to check
// the WPs via stronger-than instead of always unfolding.
[@expect_failure]
let test3 () : ND int (fun p -> p 5 /\ p 3) = 4

effect Nd (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ND a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

(* The primitive effect Tot is definitionally equal to an instance of PURE *)
effect NDTot (a:Type) = ND a (pure_null_wp a)

(* let test () : ND int (fun p -> forall (x:int). 0 <= x /\ x < 10 ==> p x) = *)
(*     let x = choose 0 1 in *)
(*     let y = choose 2 3 in *)
(*     let z = choose 4 5 in *)
(*     x + y + z *)

let test_reify_1 () = assert (reify (test1 ()) () ==  [5])
let test_reify_2 () = assert (reify (test2 ()) () ==  [3])
let test_reify_3 () = assert (reify (test1 ()) () =!= [4])
