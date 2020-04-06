module Bug1714

let arrow (a b:Type) = a -> b
unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

type p = | Print : string -> p

let rec t (b:bool) : Type0 =
  match b with
  | false -> p
  | true -> arrow int p

let run (b:bool) (f:t b) : p =
  match b with
  | false -> f
  | true ->
      let f = coerce #(arrow int (t false)) f in
      f 3

let rec t' (b:bool) : Type0 =
  match b with
  | false -> unit
  | true -> string

let run' (b:bool) (f: arrow (t' b) string) : string =
  match b with
  | false -> f ()
  | true -> f "ok"

let s:string =
  let f : t true = fun src -> Print "mov" in
  let ip = run true f in
  match ip with Print x -> "hello " ^ x

let s':string =
  run' true (fun x -> "goodbye " ^ x)
