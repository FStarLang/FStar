module BST

let max i j = if i < j then j else i

(* The type of a binary tree indexed by its max element *)
type tree: int -> Type = 
  | Leaf : n:int -> tree n
  | Node : #l:int -> left:option (tree l)
        ->  n:int
        -> #r:int -> right:option (tree r){l <= n 
                                            /\ n <= r 
                                            /\ (is_None right <==> n=r)
                                            /\ (is_None left <==> n=l)}
        -> tree r
    

val insert: #k:int -> t:tree k -> i:int -> Tot (tree (max k i)) (decreases t)
let rec insert k t i = match t with 
  | Leaf n -> 
    if i = n
    then t
    else if i < n 
    then Node (Some (Leaf i)) n #n None 
    else Node #n None n (Some (Leaf i))

  | Node #l left n #r right -> 
    if i = n 
    then t
    else if i < n
    then match left with 
      | None -> 
        Node (Some (Leaf i)) n right
      | Some left -> 
        let left' = insert left i in 
        Node (Some left') n right
    else match right with 
      | None -> 
        Node left n (Some (Leaf i))
      | Some right -> 
        let right' = insert right i in
        Node left n (Some right')
