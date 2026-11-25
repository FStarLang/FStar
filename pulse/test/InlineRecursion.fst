module InlineRecursion

#lang-pulse

open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

inline_for_extraction noextract
fn rec countdown (n:U32.t)
  returns result:U32.t
  ensures pure (result == 0ul)
  decreases (U32.v n)
{
  if (U32.eq n 0ul) { n } else { countdown (U32.sub n 1ul) }
}

fn run (n:U32.t)
  returns result:U32.t
  ensures pure (result == 0ul)
{
  countdown n
}
