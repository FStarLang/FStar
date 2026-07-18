open Prims
let showable_sys : FStarC_Platform_Base.sys FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | FStarC_Platform_Base.Unix -> "Unix"
         | FStarC_Platform_Base.Win32 -> "Win32"
         | FStarC_Platform_Base.Cygwin -> "Cygwin")
  }
let windows : Prims.bool=
  FStarC_Platform_Base.system = FStarC_Platform_Base.Win32
let cygwin : Prims.bool=
  FStarC_Platform_Base.system = FStarC_Platform_Base.Cygwin
let unix : Prims.bool=
  (FStarC_Platform_Base.system = FStarC_Platform_Base.Unix) ||
    (FStarC_Platform_Base.system = FStarC_Platform_Base.Cygwin)
let exe (s : Prims.string) : Prims.string=
  if windows then Prims.strcat s ".exe" else s
let ocamlpath_sep : Prims.string= if windows then ";" else ":"
