# lambdaLVish in Redex

lambdaLVish is the LVish calculus, but (1) renamed so as not to be
confused with the LVish Haskell library, and (2) extended with support
for `bump`.

### Version requirements

The code has been tested under
[various versions of Racket](https://travis-ci.org/lkuper/lvar-semantics).
Other versions may also work.

It will _not_ work under versions prior to 5.3.2 (released January
2013).  This is because version 5.3.2 added support for the Redex
`boolean` pattern, which the code makes use of.

### Building and running

Running `make all` in this directory will build all the lambdaLVish
languages and run their test suites.
