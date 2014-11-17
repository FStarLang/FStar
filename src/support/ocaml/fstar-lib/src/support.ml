module Prims = struct
  (* Fix this... *)
  type double  = float
  type int32 = int

  type byte = char
  type 'a list =
    | Nil
    | Cons of 'a * 'a list
  let rec nl2l = function
    | Nil -> []
    | Cons (x, xs) -> x::(nl2l xs)
  let rec l2nl = function
    | [] -> Nil
    | x::xs -> Cons (x, l2nl xs)
  let pipe_left f = f
  let pipe_right x f = f x
  let ignore _ = ()
  let fst = fst
  let snd = snd
end


module ST = struct
  let read x = !x
end


module String = struct
  let strcat s t = s^t
  let split seps s =
    let rec repeat_split acc = function
      | [] -> acc
      | sep::seps ->
         let l = BatList.flatten (BatList.map (fun x -> BatString.nsplit x (BatString.make 1 sep)) acc) in
         repeat_split l seps in
    Prims.l2nl (repeat_split [s] (Prims.nl2l seps))
  let compare x y = BatString.compare x y
end


module List = struct
  let map f nl = Prims.l2nl (BatList.map f (Prims.nl2l nl))
  let iter f nl = BatList.iter f (Prims.nl2l nl)
  let partition p nl =
    let (l1,l2) = BatList.partition p (Prims.nl2l nl) in
    (Prims.l2nl l1, Prims.l2nl l2)
  let append l1 l2 = Prims.l2nl ((Prims.nl2l l1)@(Prims.nl2l l2))
  let fold_left f a l = BatList.fold_left f a (Prims.nl2l l)
end


module Microsoft = struct
  module FStar = struct


    module Util = struct
      type 'a set = 'a Prims.list * ('a -> 'a -> bool)
      let new_set cmp _ = (Prims.Nil, fun x y -> cmp x y = 0)

      type 'v smap = (string, 'v) BatHashtbl.t

      let format (fmt:string) (args:string list) =
        let frags = BatString.nsplit fmt "%s" in
        if BatList.length frags <> BatList.length args + 1 then
          failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
        else
          let args = args@[""] in
          BatList.fold_left2 (fun out frag arg -> out ^ frag ^ arg) "" frags args
      let format1 f a = format f [a]
      let format2 f a b = format f [a;b]
      let format3 f a b c = format f [a;b;c]

      let pr  = Printf.printf
      let spr = Printf.sprintf
      let fpr = Printf.fprintf
      let print_string s = pr "%s" s

      let concat_l sep l = BatString.concat sep (Prims.nl2l l)

      let int_of_string s = BatInt.of_string s
      let hashcode s = BatHashtbl.hash s
      let compare s1 s2 = BatString.compare s1 s2

      type ('a,'b) either =
        | Inl of 'a
        | Inr of 'b

      let for_some p l = BatList.exists p (Prims.nl2l l)

      let prefix l =
        match BatList.rev (Prims.nl2l l) with
          | hd::tl -> (Prims.l2nl (BatList.rev tl), hd)
          | _ -> failwith "impossible"

      let mk_ref x = ref x
      let expand_environment_variable = Sys.getenv
    end


    module Unionfind = struct
    (* Unionfind with path compression but without ranks *)

      type 'a cell = {mutable contents : 'a contents}
       and 'a contents =
         | Data of 'a list * Prims.int32
         | Fwd of 'a cell
      type 'a uvar = 'a cell

      exception Impos

      let counter = ref 0

      let fresh x = counter := !counter + 1; {contents = Data ([x], !counter) }

      let rec rep cell = match cell.contents with
          | Data _ -> cell
          | Fwd cell' ->
             if cell == cell' then
               failwith "YIKES! Cycle in unionfind graph"
             else
               rep cell'

      let find x =
        let y = rep x in
        if not (x == y) then x.contents <- Fwd y; (* path compression *)
        match y.contents with
          | Data ((hd::tl), _) -> hd
          | _ -> failwith "impossible"

      let uvar_id uv = match (rep uv).contents with
          | Data (_, id) -> id
          | _ -> failwith "impossible"

      let union x y =
        let cellX = rep x in
        let cellY = rep y in
        if cellX == cellY then
          ()
        else
          match cellX.contents, cellY.contents with
            | Data (dx, ctrx), Data (dy,_) ->
               cellX.contents <- Data ((dx@dy), ctrx);
               cellY.contents <- Fwd cellX
            | _ -> failwith "impossible"

      let change x a =
        let cellX = rep x in
        match cellX.contents with
	  | Data (_, ctrX) ->
	     cellX.contents <- Data ([a],ctrX)
          | _ -> failwith "impossible"

      let equivalent x y =
        (rep x) == (rep y)

    end


    module Platform = struct
      let exe name =
        if Sys.unix then
          name
        else
          name^".exe"
    end


    module Getopt = struct
      let noshort='\000'
      type opt_variant =
        | ZeroArgs of (unit -> unit)
        | OneArg of (string -> unit) * string
    end


  end
end
