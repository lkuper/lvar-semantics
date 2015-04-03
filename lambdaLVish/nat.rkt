#lang racket

(module language racket
  (require "lambdaLVish.rkt")
  (require srfi/1)
  (provide lambdaLVish-nat)
  
  (define-lambdaLVish-language lambdaLVish-nat downset-op max inflationary-op natural)

  ;; To figure out at some point: maybe we could actually write
  ;; downset-op with Redex patterns?

  (define downset-op
    (lambda (d)
      (if (number? d)
          (append '(Bot) (iota d) `(,d))
          '(Bot))))

  ;; TODO: where do we test *these*?

  ;; The "bump" function.  Bumping Bot gives you 1, right?
  (define inflationary-op
    (lambda (d)
      (match d
        ['Bot 1]
        [number (add1 d)]))))

(module test-suite racket
  (require redex/reduction-semantics)
  (require (submod ".." language))
  (require "test-helpers.rkt")
  
  (provide
   test-all)

  (define (test-all)
    (display "Running metafunction tests...")
    (flush-output)
    (time (meta-test-suite))

    (display "Running test suite...")
    (flush-output)
    (time (program-test-suite rr)))

  ;; Test suite
  
  (define (meta-test-suite)
    (test-equal
     (term (exists-p (6 #f Bumpable) ()))
     (term #f))

    (test-equal
     (term (exists-p (6 #f Bumpable) ((3 #f Bumpable))))
     (term (3 #f Bumpable)))

    (test-equal
     (term (exists-p (6 #f Bumpable) ((9 #f Bumpable))))
     (term #f))

    (test-equal
     (term (exists-p (3 #f Bumpable) ((3 #f Bumpable))))
     (term (3 #f Bumpable)))

    ;; These next three are unrealistic for this lattice because Q would
    ;; be a singleton set, but it's here to exercise exists-p.
    (test-equal
     (term (exists-p (6 #f Bumpable) ((7 #f Bumpable) (8 #f Bumpable) (9 #f Bumpable))))
     (term #f))

    (test-equal
     (term (exists-p (6 #f Bumpable) ((7 #f Bumpable) (8 #f Bumpable) (9 #f Bumpable) (6 #f Bumpable))))
     (term (6 #f Bumpable)))

    (test-equal
     (term (exists-p (6 #f Bumpable) ((7 #f Bumpable) (8 #f Bumpable) (9 #f Bumpable) (5 #f Bumpable))))
     (term (5 #f Bumpable)))

    (test-equal
     (term (lub Bot Bot))
     (term Bot))

    (test-equal
     (term (lub Top 3))
     (term Top))

    (test-equal
     (term (lub 3 4))
     (term 4))

    (test-equal
     (term (lub 3 3))
     (term 3))

    (test-equal
     (term (lub-p (3 #f Puttable) (4 #f Puttable)))
     (term ((lub 3 4) #f Puttable)))

    (test-equal
     (term (lub-p (3 #t Puttable) (3 #t Puttable)))
     (term (3 #t Puttable)))

    (test-equal
     (term (lub-p (3 #t Puttable) (4 #t Puttable)))
     (term Top-p))

    (test-equal
     (term (lub-p (3 #f Puttable) (4 #t Puttable)))
     (term (4 #t Puttable)))

    (test-equal
     (term (lub-p (4 #f Puttable) (3 #t Puttable)))
     (term Top-p))

    (test-equal
     (term (lub-p (4 #t Puttable) (3 #f Puttable)))
     (term (4 #t Puttable)))

    (test-equal
     (term (lub-p (3 #t Puttable) (4 #f Puttable)))
     (term Top-p))

    (test-equal
     (term (leq 3 3))
     (term #t))

    (test-equal
     (term (leq Top 3))
     (term #f))

    (test-equal
     (term (leq 3 Top))
     (term #t))
    
    (test-equal
     (term (leq Bot 3))
     (term #t))

    (test-equal
     (term (leq 3 Bot))
     (term #f))

    (test-equal
     (term (leq Top Bot))
     (term #f))

    (test-equal
     (term (leq Bot Top))
     (term #t))

    (test-equal
     (term (leq 3 4))
     (term #t))

    (test-equal
     (term (leq 4 3))
     (term #f))

    (test-equal
     (term (extend-H () 3))
     (term (3)))

    (test-equal
     (term (extend-H (3 4 5) 6))
     (term (6 3 4 5)))

    ;; For the remaining tests, note that (downset 3) => (Bot 0 1 2 3).

    ;; The following tests all use the entire downset as Q:

    (test-equal
     (term (contains-all-Q 3
                           (Bot 0 1 2 3)
                           (Bot 0 1 2 3)))
     (term #t))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 1 2 3)
                           (Bot 0 1 2 3)))
     (term #f))

    (test-equal
     (term (contains-all-Q 3
                             (Bot 2 3)
                             (Bot 0 1 2 3)))
     (term #f))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 2 3 4 5)
                           (Bot 0 1 2 3)))
     (term #f))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 0 1 2 3 4 5)
                           (Bot 0 1 2 3)))
     (term #t))

    ;; And these use smaller sets as Q:

    (test-equal
     (term (contains-all-Q 3
                           (Bot 0 1 2 3)
                           (Bot)))
     (term #t))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 1 2 3)
                           (Bot 0)))
     (term #f))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 2 3)
                           (Bot 2 3)))
     (term #t))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 2 3 4 5)
                           (0 1 2 3)))
     (term #f))

    (test-equal
     (term (contains-all-Q 3
                           (Bot 0 1 2 3 4 5)
                           (Bot 0)))
     (term #t))

    ;; The following tests all use the entire downset as Q:

    ;; "Return the first element <= 3 that is *not* in (0 1 2 3 4 5)
    ;; but *is* in (Bot 0 1 2 3)."
    (test-equal
     (term (first-unhandled-d-in-Q 3 (0 1 2 3 4 5) (Bot 0 1 2 3)))
     (term Bot))
    
    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 1 2 3 4 5) (Bot 0 1 2 3)))
     (term 0))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 1 2 3 4 5) (Bot 0 1 2 3)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 1 2 3) (Bot 0 1 2 3)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 2 3) (Bot 0 1 2 3)))
     (term 0))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 2 3) (Bot 0 1 2 3)))
     (term 1))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 1 2) (Bot 0 1 2 3)))
     (term 3))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 1 2 4 5 6 7) (Bot 0 1 2 3)))
     (term 3))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (7 0 2 6 Bot 3 1 5 4) (Bot 0 1 2 3)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (7 6 5 4 3 0 Bot) (Bot 0 1 2 3)))
     (term 1))

    ;; And these use smaller sets as Q:

    ;; "Return the first element <= 3 that is *not* in (0 1 2 3 4 5)
    ;; but *is* in (1 2 3)."
    (test-equal
     (term (first-unhandled-d-in-Q 3 (0 1 2 3 4 5) (1 2 3)))
     (term #f))
    
    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 1 2 3 4 5) (1 2 3)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 1 2 3 4 5) (1 2 3)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 1 2 3) (1 2 3)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 2 3) (0 1 2)))
     (term 0))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 2 3) (0 1 2)))
     (term 1))

    (test-equal
     (term (first-unhandled-d-in-Q 1 (Bot 0 3) (2)))
     (term #f))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 3) (2)))
     (term 2))

    (test-equal
     (term (first-unhandled-d-in-Q 3 (Bot 0 2 3) (2)))
     (term #f))

    (test-equal
     (term (store-dom ((l1 (4 #f Puttable)) (l2 (5 #f Bumpable)) (l3 (Bot #f Puttable)))))
     (term (l1 l2 l3)))
    
    (test-equal
     (term (lookup-val ((l (2 #f Puttable))) l))
     (term 2))

    (test-equal
     (term (lookup-status ((l (2 #f Puttable))) l))
     (term #f))

    (test-equal
     (term (lookup-status ((l (2 #t Puttable))) l))
     (term #t))

    (test-equal
     (term (lookup-state ((l (2 #t Puttable))) l))
     (term (2 #t Puttable)))

    (test-equal
     (term (lookup-state ((l (2 #t Puttable)) (l1 (3 #f Puttable))) l1))
     (term (3 #f Puttable)))

    (test-equal
     (term (lookup-type ((l (2 #t Puttable)) (l1 (3 #f Puttable))) l1))
     (term Puttable))
    
    (test-equal
     (term (update-state () l (4 #f Puttable)))
     (term ((l (4 #f Puttable)))))
    
    (test-equal
     (term (update-state ((l (3 #f Puttable))) l (4 #f Puttable)))
     (term ((l (4 #f Puttable)))))

    (test-equal
     (term (update-state () l (Bot #f Puttable)))
     (term ((l (Bot #f Puttable)))))

    (test-equal
     (term (store-dom ()))
     (term ()))

    (test-equal
     (term (store-dom ((l (3 #f Puttable)) (l1 (4 #f Puttable)))))
     (term (l l1)))

    (test-equal
     (term (store-dom-diff ((l (3 #f Puttable)) (l1 (4 #f Puttable)))
                           ((l (4 #f Puttable)) (l1 (3 #f Puttable)))))
     (term ()))

    (test-equal
     (term (store-dom-diff ((l (3 #f Puttable)))
                           ((l (4 #f Puttable)) (l1 (3 #f Puttable)))))
     (term ()))

    (test-equal
     (term (store-dom-diff ((l (4 #f Puttable)) (l1 (3 #f Puttable)))
                           ((l (3 #f Puttable)))))
     (term (l1)))

    (test-equal
     (term (store-dom-diff ((l (4 #f Puttable)))
                           ()))
     (term (l)))

    (test-equal
     (term (top? Top))
     (term #t))

    (test-equal
     (term (top? Bot))
     (term #f))

    (test-equal
     (term (top? 3))
     (term #f))

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (4 #f Puttable)) (l1 (3 #f Puttable))) ())
      '(((l1 (3 #f Puttable)) (l (4 #f Puttable))) ()))
     #t)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l1 (3 #f Puttable)) (l (4 #f Puttable))) ())
      '(((l1 (3 #f Puttable)) (l (4 #f Puttable))) (3)))
     #f)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (4 #f Puttable)) (l1 (3 #f Puttable))) ())
      '(((l1 (3 #f Puttable)) (l (4 #f Puttable))) (3)))
     #f)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (3 #f Puttable)) (l1 (4 #f Puttable))) ())
      '(((l1 (3 #f Puttable)) (l (4 #f Puttable))) ()))
     #f)

    (test-equal
     (term (subst l l1 (((l (Bot #f Puttable)))
                        (put l 3))))
     (term (((l1 (Bot #f Puttable)))
            (put l1 3))))

    (test-results))

  (define (program-test-suite rr)

    (test-->> rr
              (term
               (() ;; empty store
                ((lambda (x_1) x_1)
                 ((lambda (x_1) x_1) (lambda (x_2) x_2)))))
              (term
               (()
                (lambda (x_2) x_2))))

    (test-->> rr
              (term
               (() ;; empty store
                (((lambda (x_1) x_1) (lambda (x_2) x_2))
                 (lambda (x_1) x_1))))
              (term
               (()
                (lambda (x_1) x_1))))

    (test-->> rr
              (term
               (() ;; empty store
                (((lambda (x_1) x_1) (lambda (x_2) x_2))
                 ((lambda (x_1) x_1) (lambda (x_2) x_2)))))
              (term
               (()
                (lambda (x_2) x_2))))

    (test-->> rr
              (term
               (() ;; empty store
                ((lambda (x_1) x_1) ())))
              (term
               (()
                ())))

    (test-->> rr
              (term
               (() ;; empty store
                ((lambda (x_1) x_1) (lambda (x_2) x_2))))
              (term
               (()
                (lambda (x_2) x_2))))

    (test-->> rr
              (term
               (((l (3 #f Puttable)))
                newPuttable))
              (term
               (((l (3 #f Puttable)) (l1 (Bot #f Puttable)))
                l1)))
    
    (test-->> rr
              (term
               (((l (3 #f Puttable)) (l1 (4 #f Puttable)))
                newPuttable))
              (term
               (((l (3 #f Puttable)) (l1 (4 #f Puttable)) (l2 (Bot #f Puttable)))
                l2)))

    (test-->> rr
              (term
               (((l (3 #f Puttable)))
                (put l 3)))
              (term
               (((l (3 #f Puttable)))
                ())))

    (test-->> rr
              (term
               (((l (Bot #f Puttable)))
                (put l 3)))
              (term
               (((l (3 #f Puttable)))
                ())))
    
    (test-->> rr
              (term
               (((l (2 #f Puttable)))
                (put l 3)))
              (term
               (((l (3 #f Puttable)))
                ())))

    ;; This should work because put just puts the max of the current
    ;; value and the new value.
    (test-->> rr
              (term
               (((l (2 #f Puttable)))
                (put l 1)))
              (term
               (((l (2 #f Puttable)))
                ())))
    
    ;; let
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 (lambda (x_1) x_1)))
                  (let ((x_2 (lambda (x_1) x_1)))
                    (x_1 x_2)))))
              (term
               (()
                (lambda (x_1) x_1))))

    ;; let par
    (test-->> rr
              (term
               (() ;; empty store
                (let par ((x_1 (lambda (x_1) x_1))
                          (x_2 (lambda (x_1) x_1)))
                  (x_1 x_2))))
              (term
               (()
                (lambda (x_1) x_1))))

    (test-->> rr
              (term
               (() ;; empty store
                ((lambda (x) x) newPuttable)))
              (term
               (((l (Bot #f Puttable)))
                l)))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 (put x_1 3)))
                    (let ((x_3 (get x_1 ((2 #f Puttable)))))
                      x_3)))))
              (term
               (((l (3 #f Puttable)))
                (2 #f Puttable))))
    
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par ((x_2 (put x_1 2))
                            (x_3 (put x_1 3)))
                    (get x_1 ((2 #f Puttable)))))))
              (term
               (((l (3 #f Puttable)))
                (2 #f Puttable))))

    ;; Another aspect of E-Put's behavior
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 (put x_1 5)))
                    ;; This should just take the lub of the old and new
                    ;; values, i.e., 5.
                    (let ((x_3 (put x_1 4)))
                      (get x_1 ((5 #f Puttable))))))))
              (term
               (((l (5 #f Puttable)))
                (5 #f Puttable))))

    (test-->> rr
              #:equiv cfgs-equal-modulo-perms?
              (term
               (()
                (let par ([x_1 newPuttable]
                          [x_2 newPuttable])
                  (let par ([x_3 (put x_1 3)]
                            [x_4 (put x_2 4)])
                    (get x_2 ((4 #f Puttable)))))))
              (term
               (((l (3 #f Puttable))
                 (l1 (4 #f Puttable)))
                (4 #f Puttable)))
              (term
               (((l (4 #f Puttable))
                 (l1 (3 #f Puttable)))
                (4 #f Puttable))))
    
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par ((x_2 (put x_1 2))
                            (x_3 (get x_1 ((2 #f Puttable)))))
                    (get x_1 ((2 #f Puttable)))))))
              (term
               (((l (2 #f Puttable)))
                (2 #f Puttable))))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par
                      ;; Gets stuck trying to get 4 out of x_1, then
                      ;; unstuck after the other subexpression finishes.
                      ((x_4 (let par ((x_2 (put x_1 2))
                                      (x_3 (put x_1 3)))
                              (get x_1 ((4 #f Puttable)))))
                       ;; Eventually puts 4 in x_1 after several dummy
                       ;; beta-reductions.
                       (x_5 ((lambda (x_2)
                               ((lambda (x_2)
                                  ((lambda (x_2)
                                     ((lambda (x_2)
                                        ((lambda (x_2)
                                           (put x_1 4)) ())) ())) ())) ())) ())))
                    x_4))))
              (term
               (((l (4 #f Puttable)))
                (4 #f Puttable))))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 (put x_1 3)))
                    (freeze x_1)))))
              (term
               (((l (3 #t Puttable)))
                3)))

    ;; Thresholding on frozenness.  The actual state of the LVar will
    ;; reach 3 (and so it will eventually have a downset of (Bot 0 1 2
    ;; 3), but the only elements in that set that need to be handled
    ;; are those that are members of the event set (Bot).  Hence the
    ;; callback will run only once.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par
                      ((x_2 (get x_1 ((1 #t Puttable) (2 #t Puttable) (3 #t Puttable) (4 #t Puttable))))
                       (x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                           (put x_1 3)))))
                    x_2))))
              (term
               (((l (3 #t Puttable)))
                (3 #t Puttable))))

    ;; Here we have a quasi-deterministic program where a freeze-after
    ;; and a put are racing with each other.  One of two things will
    ;; happen: (put x_1 (4)) will complete first, so x_2 will be (4),
    ;; or the freeze-after will complete first, so the program will
    ;; raise an error.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par
                      ((x_2 (let ((x_4 (put x_1 3)))
                              (freeze x_1)))
                       (x_3 (put x_1 4)))
                    x_2))))
              (term
               (((l (4 #t Puttable)))
                4))
              (term
               Error))

    ;; Fancier freezing.  This one will actually never raise an error
    ;; because the racing put is less than 2!

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par
                      ((x_2 (let ((x_4 (put x_1 0)))
                              (freeze x_1 after (Bot) with (lambda (x)
                                                             (put x_1 2)))))
                       (x_3 (put x_1 1)))
                    x_2))))
              (term
               (((l (2 #t Puttable)))
                2)))
    
    ;; But this one is quasi-deterministic: if the racing put wins,
    ;; we'll finish with 3 and no error; otherwise we'll get a
    ;; put-after-freeze error.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par
                      ((x_2 (let ((x_4 (put x_1 0)))
                              (freeze x_1 after (Bot) with (lambda (x)
                                                             (put x_1 2)))))
                       (x_3 (put x_1 3)))
                    x_2))))
              (term
               (((l (3 #t Puttable)))
                3))
              (term
               Error))

    ;; Suppose we don't do any writes to an LVar, but then we do a
    ;; freeze-after with a callback.  The callback must still run at
    ;; least once, in order to add Bot to the `handled` set.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 newPuttable))
                    (let par
                        ((x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                             (put x_2 7))))
                         (x_4 (put x_2 5)))
                      x_3)))))
              (term
               (((l (Bot #t Puttable))
                 (l1 (7 #f Puttable)))
                Bot)))

    ;; Just trying some weird things.  This program will fault if one
    ;; of the callback-triggered `put`s completes after the other LVar
    ;; gets frozen, but it's also possible for the program to complete
    ;; successfully!
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 newPuttable))
                    (let par
                        ((x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                             (put x_2 0))))
                         (x_4 (freeze x_2 after (Bot) with (lambda (x)
                                                             (put x_1 1)))))
                      x_3)))))
              (term
               (((l (1 #t Puttable))
                 (l1 (0 #t Puttable)))
                1))
              (term
               Error))

    ;; Trying out more interesting eval contexts.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 newPuttable))
                    (let ((x_3 (freeze ((lambda (x) x) x_2))))
                      x_3)))))
              (term
               (((l (Bot #f Puttable))
                 (l1 (Bot #t Puttable)))
                Bot)))
    
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 newPuttable))
                    (let par
                        ((x_3 (freeze x_1 after (Bot) with ((lambda (x)
                                                              (lambda (x)
                                                                (put x_2 0)))
                                                            ())))
                         (x_4 (freeze x_2 after (Bot) with ((lambda (x)
                                                              (lambda (x)
                                                                (put x_1 1)))
                                                            ()))))
                      x_3)))))
              (term
               (((l (1 #t Puttable))
                 (l1 (0 #t Puttable)))
                1))
              (term
               Error))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let ((x_2 newPuttable))
                    (let ((x_3 newPuttable))
                      (let par
                          ((x_3 (freeze x_1 after (Bot) with ((lambda (x)
                                                                (lambda (x)
                                                                  (put x_2 0)))
                                                              (put x_3 4))))
                           (x_4 (freeze x_2 after (Bot) with ((lambda (x)
                                                                (lambda (x)
                                                                  (put x_1 1)))
                                                              (put x_3 3)))))
                        x_3))))))
              (term
               (((l (1 #t Puttable))
                 (l1 (0 #t Puttable))
                 (l2 (4 #f Puttable)))
                1))
              (term
               Error))

    ;; Freezing an LVar twice with different values is
    ;; quasi-deterministic.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 newPuttable))
                  (let par
                        ((x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                             (put x_1 0))))
                         (x_4 (freeze x_1 after (Bot) with (lambda (x)
                                                             (put x_1 1)))))
                      x_3))))
              (term
               (((l (1 #t Puttable)))
                1))
              (term
               Error))

    (test-results)))

(module test-all racket
  (require (submod ".." test-suite))
  (test-all))
