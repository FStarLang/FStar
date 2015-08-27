module FileIO

let read (f:string) =
    System.IO.File.ReadAllText(f)

let write (f:string) (s:string) =
    System.IO.File.WriteAllText(f, s)