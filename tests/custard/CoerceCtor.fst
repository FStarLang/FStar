module CoerceCtor

(* [return]'s [Ok] is built where a [res (int & option int)] is wanted, but
   inlined out of a polymorphic definition it is typed [any].  The match it
   ends up in takes the expected type, and so must the constructor, or Cherry
   takes a [res] out of an [any] it was never put into. *)
open FStar.All

type res a = | Ok : a -> int -> res a | Err : string -> res a
let result a = string -> int -> ML (res (a & option int))

inline_for_extraction
let return (#a:Type) (x:a) : result a = fun _ c -> Ok (x, None) c
let fail_str #a (msg:string) : result a = fun _ c -> Err msg

inline_for_extraction
let (let!) (#a #b:Type) (x:result a) (y:a -> ML (result b)) : result b =
  fun ctx c -> match x ctx c with
  | Ok (v, _) c' -> y v ctx c'
  | Err m -> Err m

let rec fold (f:int -> string -> ML (result int)) (acc:int) (l:list string) : ML (result int) =
  match l with
  | [] -> return acc
  | x :: xs -> let! a = f acc x in fold f a xs

let g (l:list string) : ML (result int) =
  fold (fun n (p:string) ->
    let! s = (match (if p = "" then None else Some p) with
      | Some t -> return t
      | _ -> fail_str "unset") in
    return (n + String.length s)) 40 l

let main () : ML unit =
  match g ["a"; "b"] "" 0 with
  | Ok (s, _) _ -> FStar.IO.print_string (string_of_int s ^ "\n")
  | Err m -> FStar.IO.print_string m
