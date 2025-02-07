module Bug177

#lang-pulse
open Pulse

// Not great, but a common issue of trying to use a computation as a value
// - Expected type int
//   but !r
//   has type
//       stt int
//         (Pulse.Lib.Reference.pts_to r (*?u2491*) _)
//         (fun x ->
//             Pulse.Lib.Reference.pts_to r (*?u2491*) _ **
//             pure ((*?u2491*) _ == x))
[@@expect_failure]
fn kswap_int
  (r : ref int)
  requires pts_to r 'v
  ensures  pts_to r 'v
{
  r := !r;
}

// Much worse.
// - Ill-typed term: r := !r
// - Assertion failed
// - The SMT solver could not prove the query. Use --query_stats for more details.
[@@expect_failure]
fn kswap_t
  (#t : Type0)
  (r : ref t)
  requires pts_to r 'v
  ensures  pts_to r 'v
{
  r := !r;
}
