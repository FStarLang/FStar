module FStarC.Platform.Base

type sys =
  | Unix
  | Win32
  | Cygwin

val system : sys
