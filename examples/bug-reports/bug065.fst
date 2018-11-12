module Bug065

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2

val ind : ta:(tree -> Type) ->
          f:(t1:tree -> t2:tree -> n:int -> ta t1 -> ta t2 -> ta (Node n t1 t2)) ->
          a:(ta Leaf) -> t:tree -> (ta t)
let rec ind ta f a t =
  match t with
  | Leaf -> a
  | Node n t1 t2 -> f t1 t2 n (ind ta f a t1) (ind ta f a t2)

(* subtyping gets terribly confused here *)
#set-options "--initial_fuel 10 --max_fuel 10 --initial_ifuel 10 --max_ifuel 10"
val find' : f:(int -> Tot bool) -> t:tree -> Tot (option (x:int{f x && in_tree x t}))
let find' f = ind (fun t -> option (x:int{f x && in_tree x t}))
                  (fun t1 t2 n o1 o2 -> if f n then Some n else
                                        if Some? o1 then o1 else o2) None
