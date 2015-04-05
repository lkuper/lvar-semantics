PLT Redex models of LVar calculi
================================

[![Build Status](https://travis-ci.org/lkuper/lvar-semantics.svg?branch=master)](https://travis-ci.org/lkuper/lvar-semantics)

Subdirectories include:

  * [lambdaLVish]: a Redex model of the lambdaLVish calculus that appears in my 2015 dissertation ([see README](https://github.com/lkuper/lvar-semantics/tree/master/lambdaLVish#readme)).

  * [LVish]: a PLT Redex model of the LVish calculus that appears in our POPL 2014 paper and accompanying tech report ([see README](https://github.com/lkuper/lvar-semantics/tree/master/LVish#readme)).

  * [lambdaLVar]: a PLT Redex model of the lambdaLVar calculus that appears in our FHPC 2013 paper and accompanying tech report ([see README](https://github.com/lkuper/lvar-semantics/tree/master/lambdaLVar#readme)).

[lambdaLVish]: https://github.com/lkuper/lvar-semantics/tree/master/lambdaLVish
[LVish]: https://github.com/lkuper/lvar-semantics/tree/master/LVish
[lambdaLVar]: https://github.com/lkuper/lvar-semantics/tree/master/lambdaLVar

### Modeling lattice parameterization in Redex, or, writing macros that write Redex models

All the LVar calculi have stores containing "lattice variables", or LVars. An LVar is a mutable store location whose contents can only increase over time, where the meaning of "increase" is given by a partially ordered set, or _lattice_, that the user of the language specifies.  Different instantiations of the lattice result in different languages.

In the Redex of today, it's not possible to parameterize a language
definition by a lattice (see discussion
[here](http://stackoverflow.com/questions/15800167/plt-redex-parameterizing-a-language-definition)).  So, instead, for each one of these Redex models we define a Racket macro that takes a lattice as arugment and *generates* a Redex language definition.

#### `define-lambdaLVar-language`

For lambdaLVar, this macro is called `define-lambdaLVar-language`.  It takes the following arguments:

  * a *name*, e.g., `lambdaLVar-nat`, which becomes the `lang-name` passed to Redex's `define-language` form.
  * a *lub operation*, e.g., `max`, a Racket-level procedure that takes two lattice elements and returns a lattice element.
  * some number of Redex patterns representing *lattice elements*, not including top and bottom elements, since we add those automatically.  (Therefore, if we wanted a lattice consisting only of Top and Bot, we wouldn't pass any lattice elements to `define-LVish-language`.)

For instance, to generate a language definition called `lambdaLVar-nat` where the lattice is the natural numbers with `max` as the least upper bound, one can write:

```racket
(define-lambdaLVar-language lambdaLVar-nat max natural)
```

Here `natural` is [a pattern built into Redex](http://docs.racket-lang.org/redex/The_Redex_Reference.html?q=natural#%28tech._natural%29) that matches any exact non-negative integer.

The file `lambdaLVar/nat.rkt` contains this instantiation and a test suite of programs for `lambdaLVar-nat`.  `lambdaLVar/natpair.rkt` and `lambdaLVar/natpair-ivars.rkt` contain two more example instantiations.

#### `define-LVish-language`

For LVish, this macro is called `define-LVish-language`.  It takes the following arguments:

  * a *name*, e.g. LVish-nat, which becomes the `lang-name` passed to Redex's `define-language` form.
  * a *"downset" operation*, a Racket-level procedure that takes a lattice element and returns the (finite) set of all lattice elements that are below that element.  The downset operation is used to implement the `freeze ... after ... with` primitive in LVish.
  * a *lub operation*, a Racket-level procedure that takes two lattice elements and returns a lattice element.
  * some number of Redex patterns representing *lattice elements*, not including top and bottom elements, since we add those automatically.

For instance, to generate a language definition called `LVish-nat` where the lattice is the natural numbers with `max` as the least upper bound, one can write:

```racket
(define-LVish-language LVish-nat downset-op max natural)
```

where `natural` is a Redex pattern, as described above, and `downset-op` is defined as

```racket
(define downset-op
  (lambda (d)
    (if (number? d)
        (append '(Bot) (iota d) `(,d))
        '(Bot)))))
```

The file `LVish/nat.rkt` contains this instantiation and a test suite of programs for `LVish-nat`.  `LVish/natpair-ivars.rkt` contains another example instantiation.

#### `define-lambdaLVish-language`

For lambdaLVish, this macro is called `define-lambdaLVish-language`.  It takes the following arguments:

  * a *name*, e.g. lambdaLVish-nat, which becomes the `lang-name` passed to Redex's `define-language` form.
  * a *"downset" operation*, a Racket-level procedure that takes a lattice element and returns the (finite) set of all lattice elements that are below that element.
  * a *lub operation*, a Racket-level procedure that takes two lattice elements and returns a lattice element.
  * an *inflationary operation*, a Racket-level procedure that takes a lattice element and returns a lattice element.
  * some number of *lattice elements* represented as Redex patterns, not including top and bottom elements, since we add those automatically.

For instance, to generate a language definition called `lambdaLVish-nat` where the lattice is the natural numbers with `max` as the least upper bound, one can write:

```racket
(define-lambaLVish-language lambdaLVish-nat downset-op max inflationary-op natural)
```

where `natural` and `downset-op` are as above, and `inflationary-op` is defined as

```racket
(define inflationary-op
  (lambda (d)
    (match d
      ['Bot 1]
      [number (add1 d)]))))
```

The file `lambdaLVish/nat.rkt` contains this instantiation and a test suite of programs for `lambdaLVish-nat`.  `lambdaLVish/natpair-ivars.rkt` contains another example instantiation.

The inflationary operation is how we model arbitrary update operations.  If the Redex model matched the on-paper version of lambdaLVish, we could pass in a *set* of update operations, not just one, but this is what the model can handle for now.

## Reduction traces

One nice feature that Redex offers is the ability to see a graphical "trace" of the reduction of a term (that is, the running of a program) in DrRacket.  In order to use the trace feature with one of these Redex model, you have to first instantiate the model with a lattice.  Open the file for the instantiatiion you want to use (such as `"nat.rkt"`), and click the "Run" button to open a REPL.  Then, in the REPL:

  * Do `(require (submod "." language))`.  This will bring the definition of the reduction relation into scope.
  * Do `(require redex)`.  This will bring `traces` into scope.
  * Try tracing a term with the `traces` command: do `(traces <rr> <term>)` where `<rr>` is the reduction relation and `<term>` is some term in your instantiation of the model.  For example, for the language defined in `"nat.rkt"`, you can try:

```racket
(traces rr (term
            (()
             (let ((x_1 newPuttable))
               (let ((x_2 (put x_1 3)))
                 (freeze x_1))))))
```

This will open a window showing a reduction graph.
