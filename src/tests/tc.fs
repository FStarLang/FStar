module FStar.Tests.Tc
open Expecto

let tests =
  testCase "A simple test" <| fun () ->
    let subject = "Hello world"
    Expect.equal subject "Hello World"
                 "The strings should equal"

let main args =
  runTestsWithArgs defaultConfig args tests

