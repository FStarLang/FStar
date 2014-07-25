(* -------------------------------------------------------------------- *)
type item =
| IInt    : int -> item
| IString : string -> item
| IUser   : ('a -> string) * 'a -> item

(* -------------------------------------------------------------------- *)
let string_of_item = function
  | IInt    i      -> string_of_int i
  | IString s      -> s
  | IUser   (f, x) -> f x

(* -------------------------------------------------------------------- *)
let print (s : string) (items : item list) =
  let isdigit = function '0'..'9' -> true | _ -> false in

  let buffer = Buffer.create 0 in
  let pos = ref 0 in

  while !pos < String.length s do
    if s.[!pos] <> '{' then
      Buffer.add_char buffer s.[!pos]
    else begin
      let pos2 = ref (pos + 1) in

      while  do



    end
  done;
  Buffer.contents buffer

(* -------------------------------------------------------------------- *)
let print1 s i1          = print s [i1]
let print2 s i1 i2       = print s [i1; i2]
let print3 s i1 i2 i3    = print s [i1; i2; i3]
let print4 s i1 i2 i3 i4 = print s [i1; i2; i3; i4]
