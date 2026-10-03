module Bug2169b

module T = FStar.Tactics.V2

(* The identity monad, without the WP index. *)
let repr (a:Type u#a) : Type u#a = a

let return (a:Type) (x:a) : repr a = x

let bind (a b:Type) (v:repr a) (f:a -> repr b) : repr b = f v

total
reifiable
reflectable
effect {
  ND with { repr; return; bind }
}

let lift_pure_nd (a:Type) (f:unit -> a) : repr a = f ()

sub_effect Tot ~> ND = lift_pure_nd

type box a = | Box of a

let g (x:int) : box int = Box x

let rewrite_inside_reify (f : int -> ND unit) (x' : int) : Tot unit =
  let _ = f in
  match g x' with
  | Box x ->
     match x with
     | 0 ->
       let unfold ll = reify (f x) in
       assert (ll == ll) by begin
         let beq = T.nth_var (-1) in
         T.rewrite beq;
         ()
       end
     | _ -> ()
