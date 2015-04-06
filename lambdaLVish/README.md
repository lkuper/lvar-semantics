# lambdaLVish in Redex

The code in this directory is a PLT Redex model of the lambdaLVish calculus from chapter 3 of [my dissertation](https://github.com/lkuper/dissertation).  lambdaLVish is similar to [the LVish calculus](https://github.com/lkuper/lvar-semantics/tree/master/LVish#readme), but (1) renamed so as not to be confused with [the LVish Haskell library](http://hackage.haskell.org/package/lvish), and (2) extended with support for arbitrary *update operations*.  Update operations generalize the `put` operation to allow not only least-upper-bound writes, but any inflationary and commutative write.

### Version requirements

The code has been tested under [various versions of Racket](https://travis-ci.org/lkuper/lvar-semantics).  Other versions may also work.

It will _not_ work under versions prior to 5.3.2 (released January 2013).  This is because version 5.3.2 added support for the Redex `boolean` pattern, which the code makes use of.

### Building and running

Running `make all` in this directory will build all the lambdaLVish languages and run their test suites.
