module Bug1622

let sprop = bool -> prop

let pred (args: list bool) : sprop =
  let rec aux (args:list bool) (out:sprop) : sprop =
  match args with
  | [] -> out
  | a::q -> let out:sprop = fun s0 -> out s0 in aux q out
  in aux args (fun _ -> True)

let lemma_pred (args:list bool) : Lemma (pred args true) =
  match args with
  | [] -> assert_norm (pred args true)
  | _ -> admit()

let lemma_pred' (args:list bool) : Lemma (pred args true) =
  match args with
  | [] -> assert_norm (pred [] true)
  | _ -> admit()
