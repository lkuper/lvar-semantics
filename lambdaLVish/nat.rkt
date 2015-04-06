#lang racket

(module language racket
  (require "lambdaLVish.rkt")
  (require srfi/1)
  (provide lambdaLVish-nat)
  
  (define-lambdaLVish-language lambdaLVish-nat downset-op max update-ops natural)

  ;; To figure out at some point: maybe we could actually write
  ;; downset-op with Redex patterns?

  (define downset-op
    (lambda (d)
      (if (number? d)
          (append '(Bot) (iota d) `(,d))
          '(Bot))))

  (define update-op-1
    (lambda (d)
      (match d
        ['Bot 1]
        [number (add1 d)])))

  (define update-op-2
    (lambda (d)
      (match d
        ['Bot 2]
        [number (add1 (add1 d))])))

  (define update-ops `(,update-op-1 ,update-op-2)))

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
     (term (exists-p (6 #f) ()))
     (term #f))

    (test-equal
     (term (exists-p (6 #f) ((3 #f))))
     (term (3 #f)))

    (test-equal
     (term (exists-p (6 #f) ((9 #f))))
     (term #f))

    (test-equal
     (term (exists-p (3 #f) ((3 #f))))
     (term (3 #f)))

    ;; These next three are unrealistic for this lattice because Q would
    ;; be a singleton set, but it's here to exercise exists-p.
    (test-equal
     (term (exists-p (6 #f) ((7 #f) (8 #f) (9 #f))))
     (term #f))

    (test-equal
     (term (exists-p (6 #f) ((7 #f) (8 #f) (9 #f) (6 #f))))
     (term (6 #f)))

    (test-equal
     (term (exists-p (6 #f) ((7 #f) (8 #f) (9 #f) (5 #f))))
     (term (5 #f)))

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
     (term (lub-p (3 #f) (4 #f)))
     (term ((lub 3 4) #f)))

    (test-equal
     (term (lub-p (3 #t) (3 #t)))
     (term (3 #t)))

    (test-equal
     (term (lub-p (3 #t) (4 #t)))
     (term Top-p))

    (test-equal
     (term (lub-p (3 #f) (4 #t)))
     (term (4 #t)))

    (test-equal
     (term (lub-p (4 #f) (3 #t)))
     (term Top-p))

    (test-equal
     (term (lub-p (4 #t) (3 #f)))
     (term (4 #t)))

    (test-equal
     (term (lub-p (3 #t) (4 #f)))
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
     (term (store-dom ((l1 (4 #f)) (l2 (5 #f)) (l3 (Bot #f)))))
     (term (l1 l2 l3)))
    
    (test-equal
     (term (lookup-val ((l (2 #f))) l))
     (term 2))

    (test-equal
     (term (lookup-status ((l (2 #f))) l))
     (term #f))

    (test-equal
     (term (lookup-status ((l (2 #t))) l))
     (term #t))

    (test-equal
     (term (lookup-state ((l (2 #t))) l))
     (term (2 #t)))

    (test-equal
     (term (lookup-state ((l (2 #t)) (l1 (3 #f))) l1))
     (term (3 #f)))

    (test-equal
     (term (update-state () l (4 #f)))
     (term ((l (4 #f)))))
    
    (test-equal
     (term (update-state ((l (3 #f))) l (4 #f)))
     (term ((l (4 #f)))))

    (test-equal
     (term (update-state () l (Bot #f)))
     (term ((l (Bot #f)))))

    (test-equal
     (term (store-dom ()))
     (term ()))

    (test-equal
     (term (store-dom ((l (3 #f)) (l1 (4 #f)))))
     (term (l l1)))

    (test-equal
     (term (store-dom-diff ((l (3 #f)) (l1 (4 #f)))
                           ((l (4 #f)) (l1 (3 #f)))))
     (term ()))

    (test-equal
     (term (store-dom-diff ((l (3 #f)))
                           ((l (4 #f)) (l1 (3 #f)))))
     (term ()))

    (test-equal
     (term (store-dom-diff ((l (4 #f)) (l1 (3 #f)))
                           ((l (3 #f)))))
     (term (l1)))

    (test-equal
     (term (store-dom-diff ((l (4 #f)))
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
      '(((l (4 #f)) (l1 (3 #f))) ())
      '(((l1 (3 #f)) (l (4 #f))) ()))
     #t)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l1 (3 #f)) (l (4 #f))) ())
      '(((l1 (3 #f)) (l (4 #f))) (3)))
     #f)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (4 #f)) (l1 (3 #f))) ())
      '(((l1 (3 #f)) (l (4 #f))) (3)))
     #f)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (3 #f)) (l1 (4 #f))) ())
      '(((l1 (3 #f)) (l (4 #f))) ()))
     #f)

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
               (((l (3 #f)))
                new))
              (term
               (((l (3 #f)) (l1 (Bot #f)))
                l1)))
    
    (test-->> rr
              (term
               (((l (3 #f)) (l1 (4 #f)))
                new))
              (term
               (((l (3 #f)) (l1 (4 #f)) (l2 (Bot #f)))
                l2)))

    (test-->> rr
              (term
               (((l (3 #f)))
                (puti l 1)))
              (term
               (((l (4 #f)))
                ())))

    (test-->> rr
              (term
               (((l (3 #f)))
                (puti l 2)))
              (term
               (((l (5 #f)))
                ())))

    (test-->> rr
              (term
               (((l (Bot #f)))
                (puti l 1)))
              (term
               (((l (1 #f)))
                ())))
    
    (test-->> rr
              (term
               (((l (2 #f)))
                (puti l 1)))
              (term
               (((l (3 #f)))
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
                ((lambda (x) x) new)))
              (term
               (((l (Bot #f)))
                l)))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 (puti x_1 1)))
                    (let ((x_3 (get x_1 ((1 #f)))))
                      x_3)))))
              (term
               (((l (1 #f)))
                (1 #f))))
    
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par ((x_2 (puti x_1 1))
                            (x_3 (puti x_1 1)))
                    (get x_1 ((2 #f)))))))
              (term
               (((l (2 #f)))
                (2 #f))))

    (test-->> rr
              (term
               (()
                (let par ([x_1 new]
                          [x_2 new])
                  (let par ([x_3 (puti x_1 1)]
                            [x_4 (puti x_2 1)])
                    (get x_2 ((1 #f)))))))
              (term
               (((l (1 #f))
                 (l1 (1 #f)))
                (1 #f))))
    
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par ((x_2 (puti x_1 1))
                            (x_3 (get x_1 ((1 #f)))))
                    (get x_1 ((1 #f)))))))
              (term
               (((l (1 #f)))
                (1 #f))))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                      ;; Gets stuck trying to get 3 out of x_1, then
                      ;; unstuck after the other subexpression finishes.
                      ((x_4 (let par ((x_2 (puti x_1 1))
                                      (x_3 (puti x_1 1)))
                              (get x_1 ((3 #f)))))
                       ;; Eventually puts 3 in x_1 after several dummy
                       ;; beta-reductions.
                       (x_5 ((lambda (x_2)
                               ((lambda (x_2)
                                  ((lambda (x_2)
                                     ((lambda (x_2)
                                        ((lambda (x_2)
                                           (puti x_1 1)) ())) ())) ())) ())) ())))
                    x_4))))
              (term
               (((l (3 #f)))
                (3 #f))))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 (puti x_1 1)))
                    (freeze x_1)))))
              (term
               (((l (1 #t)))
                1)))

    ;; Thresholding on frozenness.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                      ((x_2 (get x_1 ((1 #t))))
                       (x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                           (puti x_1 1)))))
                    x_2))))
              (term
               (((l (1 #t)))
                (1 #t))))

    ;; Mixing different update operations is fine, since they commute.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                      ((x_2 (puti x_1 1))
                       (x_3 (puti x_1 2)))
                    (freeze x_1)))))
              (term
               (((l (3 #t)))
                3)))

    ;; Here we have a quasi-deterministic program where a freeze and a
    ;; put are racing with each other.  One of two things will happen:
    ;; both `puti`s will run before the freeze, so x_1 will be 2, or
    ;; the freeze will complete before both `puti`s have run, so the
    ;; program will raise an error.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                      ((x_2 (let ((x_4 (puti x_1 1)))
                              (freeze x_1)))
                       (x_3 (puti x_1 1)))
                    x_2))))
              (term
               (((l (2 #t)))
                2))
              (term
               Error))

    ;; Similar to the above, but with `freeze ... after ... with` and
    ;; an additional `puti`.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                      ((x_2 (let ((x_4 (puti x_1 1)))
                              (freeze x_1 after (Bot) with (lambda (x)
                                                             (puti x_1 1)))))
                       (x_3 (puti x_1 1)))
                    x_2))))
              (term
               (((l (3 #t)))
                3))
              (term
               Error))

    ;; Suppose we don't do any writes to an LVar, but then we do a
    ;; freeze-after with a callback.  The callback must still run at
    ;; least once, in order to add Bot to the `handled` set.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 new))
                    (let par
                        ((x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                             (puti x_2 1))))
                         (x_4 (puti x_2 1)))
                      x_3)))))
              (term
               (((l (Bot #t))
                 (l1 (2 #f)))
                Bot)))

    ;; Just trying some weird things.  This program will fault if one
    ;; of the callback-triggered `puti`s completes after the other LVar
    ;; gets frozen, but it's also possible for the program to complete
    ;; successfully!
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 new))
                    (let par
                        ((x_3 (freeze x_1 after (Bot) with (lambda (x)
                                                             (puti x_2 1))))
                         (x_4 (freeze x_2 after (Bot) with (lambda (x)
                                                             (puti x_1 1)))))
                      x_3)))))
              (term
               (((l (1 #t))
                 (l1 (1 #t)))
                1))
              (term
               Error))

    ;; Trying out more interesting eval contexts.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 new))
                    (let ((x_3 (freeze ((lambda (x) x) x_2))))
                      x_3)))))
              (term
               (((l (Bot #f))
                 (l1 (Bot #t)))
                Bot)))
    
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 new))
                    (let par
                        ((x_3 (freeze x_1 after (Bot) with ((lambda (x)
                                                              (lambda (x)
                                                                (puti x_2 1)))
                                                            ())))
                         (x_4 (freeze x_2 after (Bot) with ((lambda (x)
                                                              (lambda (x)
                                                                (puti x_1 1)))
                                                            ()))))
                      x_3)))))
              (term
               (((l (1 #t))
                 (l1 (1 #t)))
                1))
              (term
               Error))

    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 new))
                    (let ((x_3 new))
                      (let par
                          ((x_3 (freeze x_1 after (Bot) with ((lambda (x)
                                                                (lambda (x)
                                                                  (puti x_2 1)))
                                                              (puti x_3 1))))
                           (x_4 (freeze x_2 after (Bot) with ((lambda (x)
                                                                (lambda (x)
                                                                  (puti x_1 1)))
                                                              (puti x_3 1)))))
                        x_3))))))
              (term
               (((l (1 #t))
                 (l1 (1 #t))
                 (l2 (2 #f)))
                1))
              (term
               Error))

    ;; Freezing an LVar twice with different values is
    ;; quasi-deterministic.
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                        ((x_3 (freeze x_1 after (Bot) with ((lambda (x)
                                                              (lambda (x)
                                                                (puti x_1 1)))
                                                            (puti x_1 1))))
                         (x_4 (freeze x_1 after (Bot) with (lambda (x)
                                                             (puti x_1 1)))))
                      x_3))))
              (term
               (((l (3 #t)))
                3))
              (term
               Error))

    (test-results)))

(module test-all racket
  (require (submod ".." test-suite))
  (test-all))
