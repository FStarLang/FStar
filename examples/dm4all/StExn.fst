module StExn

open FStar.List
open FStar.WellFounded
open FStar.Tactics

(* Reasoning about State plus exceptions, but WPs only over
 * the stateful part. Exceptions are all failures. *)

type state = int

let st a = state -> option (a * state)

let return (a:Type) (x:a) = fun s -> Some (x, s)

let bind (a : Type u#aa) (b : Type u#bb)
         (m : st a) (f : a -> st b) : st b =
  fun s -> match m s with
        | Some (v, s') -> f v s'
        | None -> None

let post a = a -> state -> Type0
let wpty a = state -> post a -> Type0

let return_wp (a:Type) (x:a) : wpty a =
  fun h p -> p x h

unfold
val bind_wp : range -> a:Type -> b:Type -> wpty a -> (a -> wpty b) -> wpty b

unfold
let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun h p -> w h (fun x h' -> kw x h' (fun y h'' -> p y h''))
  
let rec interpretation #a (m : st a) (s0 : state) (p : post a) : Type0 =
  match m s0 with
  | Some (x, s1) -> p x s1
  | None -> False

total
reifiable
reflectable
new_effect {
  StExn : a:Type -> Effect
  with
       repr      = st
     ; return    = return
     ; bind      = bind

     ; wp_type   = wpty
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; interp = interpretation
}

val get : unit -> StExn state (fun s p -> p s s)
let get () =
  StExn?.reflect (fun s -> Some (s,s))

val set : s:state -> StExn unit (fun _ p -> p () s)
let set s =
  StExn?.reflect (fun _ -> Some ((), s))

let raise () : StExn unit (fun _ _ -> False) =
  StExn?.reflect (fun s -> None)

let test1 () : StExn int (fun s0 p -> p 42 (s0 + 5)) =
  let x = get () in
  set (x + 2);
  let y = get () in
  set (y + 3);
  42

[@(expect_failure [19])]
let test2 () : StExn int (fun s0 p -> p 42 (s0 + 5)) =
  let x = get () in
  if x < 1 then raise ();
  set (x + 2);
  let y = get () in
  set (y + 3);
  42

let test3 () : StExn int (fun s0 p -> s0 >= 1 /\ p (s0 + 2) (s0 + 5)) =
  let x = get () in
  if x < 1 then raise ();
  set (x + 2);
  let y = get () in
  set (y + 3);
  y
