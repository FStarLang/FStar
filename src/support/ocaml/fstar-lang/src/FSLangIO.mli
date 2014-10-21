(* -------------------------------------------------------------------- *)
type program = unit

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> program
val from_file    : string -> program
val from_string  : string -> program
