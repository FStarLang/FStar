#light "off"
module FStar_All
  let failwith x = failwith x
  let exit i = exit i
  let pipe_right a f = f a
  let pipe_left f a = f a
  let try_with f1 f2 = try f1 () with | e -> f2 e
