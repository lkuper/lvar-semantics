# lambdaLVar in Redex

The code in this directory is a PLT Redex model of the lambdaLVar calculus in the paper ["LVars: Lattice-based Data Structures for Deterministic Parallelism"][lambdaLVar-paper] (with some differences, as described below).

**Stop!**  Are you sure this is what you want to be looking at?  If you're interested in LVars, you're probably better off looking at what's in the [LVish](https://github.com/lkuper/lvar-semantics/tree/master/LVish) or [lambdaLVish](https://github.com/lkuper/lvar-semantics/tree/master/lambdaLVish) directories instead.  This stuff is just here for historical reasons.

### lambdaLVar in a nutshell

lambdaLVar is a deterministic parallel calculus with shared state.  It is an untyped lambda calculus extended with a store and with `put` and `get` operations that write to and read from shared variables.  In this setting of shared mutable state, the trick that lambdaLVar employs to maintain determinism is that writes must be _monotonically increasing_ with respect to a user-specified partial order, and reads must make only limited observations of the states of variables -- for instance, in a lambdaLVar program it might be possible to observe that a store location containes "at least 4", but not possible to observe the precise value.

### Modeling truly simultaneous reductions in Redex

With Redex, one typically defines a [Felleisen-and-Hieb-style reduction semantics based on _evaluation contexts_][eval-contexts]. An evaluation-context-based semantics is what Redex is best at expressing, and such a semantics would eliminate the need to explicitly specify "structural" rules like E-Put-1 and E-Put-2 in our semantics.  Instead, we could simply specify a set of evaluation contexts:

```
(E hole (put E e) (put e E) ...)
```

Unfortunately, such _single-hole_ evaluation contexts force evaluation to be sequential, and we want to model the explicit simultaneous evaluation steps of the E-ParApp rule of our semantics.  (To be sure, a semantics specified with single-hole evaluation contexts can express _arbitrary_ evaluation order and therefore remains open to the possibility of parallel _implementation_. Still, since parallelism is lambdaLVar's _raison d'être_, we want to bake parallelism into the model.)

Since Redex [does not have support for multiple-hole evaluation contexts][racket-list-message], we opted instead for an inference-rule-based semantics implemented using Redex's [`define-judgment-form`][define-judgment-form] feature.  Unfortunately, in so doing, we miss out on some of Redex's most useful features.  ~~As a tiny example of what we're missing, `define-judgment-form` offers no way to name individual reduction rules, so although using Redex's [`traces`][traces] feature with our semantics will show us a beautiful reduction graph of a configuration, it won't label the edges in the graphs with the names of the reduction rules as it would normally, because Redex has no way of knowing their names.~~ Actually, this is no longer true -- the ability to name clauses in `define-judgment-form` was added in Racket release 5.3.1.  But it's still going to take additional effort to get the names of rules to appear in the visualization.

The Redex model is useful despite these limitations.  However, it would be interesting to try modeling lambdaLVar in a framework that has better support for truly simultaneous reductions -- the [K system][k-framework] comes to mind.

### Dealing with reflexive relations

The reflexive reduction rules E-Refl and E-ReflErr of our paper semantics pose a dilemma for the Redex testing infrastructure. Redex's built-in `test-->>` mechanism for testing a reduction relation finds all irreducible terms reachable from a given term, but with E-Refl and E-ReflErr present in the reduction relation, no lambdaLVar terms would be irreducible under it, so it wouldn't be possible to write tests with `test-->>`.  An alternative testing mechanism, `test-->>E`, checks if there _exists_ a reduction path from one given term to another, but since the property we are most interested in testing for is determinism, that mechanism is also unsatisfactory since we wish to know not only that one term reduces to another, but that _all_ possible reductions take us from the first to the second.

Fortunately, there is a simple workaround: we drop the E-Refl and E-ReflErr rules from our semantics and instead add two new rules, E-App-1 and E-App-2, by which parallel application expressions may take a step even if only one of their subexpressions can take a step.  The result is a semantics that is feasible to test with Redex.  This reduction relation is called `slow-rr`.

### Speed tweaks

Under the semantics just described, if both subexpressions in an application can step, then any of three rules can apply next -- E-App-1, E-App-2, and E-ParApp -- leading to an exponential increase in the number of evaluation paths that an configuration might take. It is easy to construct lambdaLVar programs that are very slow to test with `test-->>` under this semantics, because the system must take all evaluation paths.  Of course, taking all evaluation paths is exactly the behavior we want.  Although we can't prove determinism with Redex, we _can_ prove the _absence_ of determinism -- a reduction graph that does not converge means that there's a nondeterminism-introducing bug somewhere.  Nevertheless, sometimes we just want to check that a program runs at all.  In that case, to ameliorate the slowness, we can define more restricted versions of E-App-1 and E-App-2, in which the subexpression that is not taking a step must be a _value_.  Finally, we add an E-GetValBlock rule, which allows a _blocked_ `get` expression to step to itself. This is necessary because a blocked `get` is not a value.  We call the resulting reduction relation `fast-rr`.

Under the `fast-rr` rules, an application expression in which one subexpression is a blocked `get` will always be able to take a step under one of the three application rules, but not all thread interleavings will be explored.  The speed boost we get from that comes at the price of modeling only a less realistic class of implementations in which parallel evaluation is ``lockstep''.

### Version requirements

The code has been tested under [various versions of Racket](https://travis-ci.org/lkuper/lvar-semantics).  Other versions may also work.

### Building and running

Running `make all` in this directory will build all the lambdaLVar languages and run their test suites, using both reduction relations.  Be warned: in the test suite for the `lambdaLVar-nat` language, there's one particular that runs so slowly under `slow-rr` that we put it in a "slow test suite" by itself. (To avoid the slow test, simply run `make`.)

```
Running metafunction tests...All 57 tests passed.
cpu time: 14 real time: 13 gc time: 0
Running test suite with fast-rr...All 19 tests passed.
cpu time: 127 real time: 128 gc time: 16
Running test suite with slow-rr...All 19 tests passed.
cpu time: 486 real time: 486 gc time: 8
Running slow test suite with fast-rr...One test passed.
cpu time: 153 real time: 154 gc time: 4
Running slow test suite with slow-rr...One test passed.
cpu time: 365914 real time: 365523 gc time: 7949
```

The slow test takes several orders of magnitude longer when run with `slow-rr` than with `fast-rr`.  Stepping through the test manually using `traces` finds 64 terms for the slow version, and 15 for the
fast version.

[lambdaLVar-paper]: http://www.cs.indiana.edu/~lkuper/papers/lvars-fhpc13.pdf

[eval-contexts]: http://www.ccs.neu.edu/racket/pubs/tcs92-fh.pdf

[racket-list-message]: http://lists.racket-lang.org/users/archive/2012-July/053000.html

[define-judgment-form]: http://docs.racket-lang.org/redex/Other_Relations.html#%28form._%28%28lib._redex/reduction-semantics..rkt%29._define-judgment-form%29%29

[traces]: http://docs.racket-lang.org/redex/GUI.html?q=traces#%28def._%28%28lib._redex/gui..rkt%29._traces%29%29

[k-framework]: http://k-framework.org
