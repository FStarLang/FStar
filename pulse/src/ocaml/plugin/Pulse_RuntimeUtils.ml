let extend_context (s:string) (c:string list) = s::c
let print_exn (e:exn) = Printexc.to_string e
