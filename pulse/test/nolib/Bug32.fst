module Bug32
open Pulse.Nolib
#lang-pulse

[@@expect_failure [189]]
ghost fn test ()
{
  rewrite emp as (if true then emp else 1);
  admit();
}