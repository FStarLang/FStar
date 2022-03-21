module Bug2146

(* This file should work anyway, but the bug we're checking for was at
desugaring time, so even --lax took forever. It should take about a
second. Without --lax, this takes about 30 seconds since it builds a big
VC. *)

#set-options "--lax"

let f (args:list int) : int =
  match args with
  | [f1; f2; f3; f4; f5; f6; f7; f8; f9; f10; f11; f12; f13; f14; f15; f16; f17; f18; f19; f20; f21; f22; f23; f24; f25; f26; f27; f28; f29; f30; f31; f32; f33; f34; f35; f36; f37; f38; f39; f40; f41; f42; f43; f44; f45; f46; f47; f48; f49; f50] ->
    0
  | _ -> 1
