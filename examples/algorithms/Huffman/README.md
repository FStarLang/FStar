To run sample

One time build UlibFS in F#
```
make -C src ulib-in-fsharp
```

And now, usual dotnet process.
```
dotnet build
dotnet fsi Huffman.fsx
```