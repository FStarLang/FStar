module StExnPartial

(* Reasoning about State plus exceptions, but WPs only over
 * the stateful part. Exceptions are all taken as success, i.e.,
 * we consider partial correctness only. *)

type state = int

let st a = state -> option (a * state)

let return (a:Type) (x:a) : st a = fun s -> Some (x, s)

let bind (a b : Type) (m : st a) (f : a -> st b) : st b =
  fun s -> match m s with
        | Some (v, s') -> f v s'
        | None -> None

let post a = a -> state -> Type0
let wpty a = state -> post a -> Type0

let return_wp (a:Type) (x:a) : wpty a =
  fun h p -> p x h

unfold
let bind_wp (_ : range) (a:Type) (b:Type) (w : wpty a) (kw : a -> wpty b) : wpty b =
  fun h p -> w h (fun x h' -> kw x h' (fun y h'' -> p y h''))

let interpretation #a (m : st a) (s0 : state) (p : post a) : Type0 =
  match m s0 with
  | Some (x, s1) -> p x s1
  | None -> True

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

     ; interp    = interpretation
}

(* Actions *)
val get : unit -> StExn state (fun s p -> p s s)
let get () =
  StExn?.reflect (fun s -> Some (s,s))

val set : s:state -> StExn unit (fun _ p -> p () s)
let set s =
  StExn?.reflect (fun _ -> Some ((), s))

let raise () : StExn unit (fun _ _ -> True) =
  StExn?.reflect (fun s -> None)

let test1 () : StExn int (fun s0 p -> p 42 (s0 + 5)) =
  let x = get () in
  set (x + 2);
  let y = get () in
  set (y + 3);
  42

(* This can raise an exception, since the initial state could be < 1,
 * but since we're doing partial correctness it is accepted *)
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
