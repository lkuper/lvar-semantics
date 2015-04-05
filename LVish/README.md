# LVish in Redex

The code in this directory is a PLT Redex model of the lambdaLVar calculus in the paper ["Freeze After Writing: Quasi-Deterministic Parallel Programming with LVars"][http://www.cs.indiana.edu/~lkuper/papers/lvish-popl14.pdf].

### Version requirements

The code has been tested under [various versions of Racket](https://travis-ci.org/lkuper/lvar-semantics).  Other versions may also work.

It will _not_ work under versions prior to 5.3.2 (released January 2013).  This is because version 5.3.2 added support for the Redex `boolean` pattern, which the code makes use of.

### Building and running

Running `make all` in this directory will build all the LVish languages and run their test suites.
