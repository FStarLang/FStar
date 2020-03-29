module Bug1682

assume val f: (n:int) -> GTot int

let test (n:int) =
  calc (==) {
    f 1;
    == { admit() }
    f 2;
  }
