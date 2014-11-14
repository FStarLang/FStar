module Prims = struct
  type byte = char
  type double  = float
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
  let exit i = exit (Int32.to_int i)
end


module ST = struct
  let read x = !x
end


module String = struct
  let strcat s t = s^t
end


module List = struct
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

      let int_of_string (s:string) = BatInt32.of_string s

      type ('a,'b) either =
        | Inl of 'a
        | Inr of 'b

      let for_some p l = BatList.exists p (Prims.nl2l l)

      let mk_ref x = ref x
      let expand_environment_variable = Sys.getenv
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
