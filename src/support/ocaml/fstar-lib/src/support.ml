module Prims = struct
  type 'a list =
    | Nil
    | Cons of 'a * 'a list
  let rec nl2l = function
    | Nil -> []
    | Cons (x, xs) -> x::(nl2l xs)
  let rec l2nl = function
    | [] -> Nil
    | x::xs -> Cons (x, l2nl xs)
  let pipe_left f x = f x
  let pipe_right x f = f x
  let ignore _ = ()
end


module ST = struct
  let read x = !x
end


module String = struct
  let strcat s t = s^t
end


module List = struct
  let iter f nl = List.iter f (Prims.nl2l nl)
end


module Microsoft = struct
  module FStar = struct


    module Util = struct
      let pr  = Printf.printf
      let spr = Printf.sprintf
      let fpr = Printf.fprintf
      let print_string s = pr "%s" s

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


  end
end
