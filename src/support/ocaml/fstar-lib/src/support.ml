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
end


module Microsoft = struct
  module FStar = struct


    module Util = struct
      let mk_ref x = ref x
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
