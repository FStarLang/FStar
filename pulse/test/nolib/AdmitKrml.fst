module AdmitKrml

#lang-pulse
open Pulse.Nolib

fn test (b : bool)
  returns x : UInt32.t
{
  if (b) {
    111ul;
  } else {
    admit();
    222ul;
  }
}
