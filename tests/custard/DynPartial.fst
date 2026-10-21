module DynPartial

(* A definition partially applied, to a function whose parameter is [any]
   ([FStarC.TypeChecker.Primops.Array.ops]): the name is typed at what
   remains of its arrow, so the arguments it is given must be checked
   against its signature's parameters instead. *)

open FStar.All
module D = FStar.Dyn

type interp_t = int -> bool -> list int -> list (int & bool) -> ML (option string)

let mixed
  (as_a : (int & bool) -> ML (option 'a))
  (as_b : (int & bool) -> ML (option 'b))
  (embed_c : int -> 'c -> ML string)
  (f : int -> list int -> 'a -> 'b -> ML (option 'c))
  (psc : int) (norm : bool) (univs : list int) (args : list (int & bool))
  : ML (option string) =
  match args with
  | [a; b] ->
    (match as_a a, as_b b with
     | Some a, Some b ->
       (match f psc univs a b with
        | Some c -> Some (embed_c psc c)
        | _ -> None)
     | _ -> None)
  | _ -> None

type blob = d:D.dyn{D.dyn_has_ty d int}

let ops (k:int) : ML (list (string & int & interp_t)) =
  let arg1 (x:(int & bool)) : option int = Some (fst x) in
  let arg2 (x:(int & bool)) : ML (option blob) =
    if snd x then Some (D.mkdyn (fst x + k)) else None in
  let length_op =
    let embed_int (r:int) (i:int) : ML string = string_of_int (r + i) in
    let run_op (b:blob) : ML (option int) = Some (D.undyn b) in
    ("len", 2, mixed arg1 arg2 embed_int (fun _r _univs _ b -> run_op b))
  in
  [length_op]

let main () : ML unit =
  match ops 1 with
  | [(_, _, f)] ->
    (match f 0 true [] [(1, true); (40, true)] with
     | Some s -> FStar.IO.print_string (s ^ "\n")
     | None -> FStar.IO.print_string "none\n")
  | _ -> ()
