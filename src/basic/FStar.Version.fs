module FStar.Version

let dummy () = ()

let _ =
  // Effects are wonderful
  FStar.Options._version  := "unknown F# version";
  FStar.Options._platform := "unknown platform";
  FStar.Options._compiler := "unknown compiler";
  FStar.Options._date     := "unknown date";
  FStar.Options._commit   := "unknown commit"
