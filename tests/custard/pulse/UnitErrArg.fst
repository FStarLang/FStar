module UnitErrArg
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

(* A parameter whose type is a [match] that reduces to [unit], as in
   EverParse's [err:(if use_error_handler then error_handler else unit)].
   The type of [f] and its call must agree on whether that parameter is
   kept, however the type was elaborated. *)
inline_for_extraction noextract
let m (b:bool) =
  s:U32.t -> err:(if b then U32.t else unit) -> x:U32.t -> stt U32.t emp (fun _ -> emp)

inline_for_extraction noextract
fn wrap (#b:bool) (g: U32.t -> bool) (f: m b) : m b =
  (s:_) (err:_) (x:_)
{
  let ok = g s;
  if ok { f s err x } else { x }
}

fn test (f: m false) (s:U32.t) (x:U32.t)
returns U32.t
{
  wrap #false (fun _ -> true) f s () x
}

fn main ()
  returns r: FStar.Int32.t
{
  0l
}
