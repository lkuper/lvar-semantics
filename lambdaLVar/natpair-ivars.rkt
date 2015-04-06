#lang racket

(module language racket
  (require redex/reduction-semantics)
  (require "lambdaLVar.rkt")

  (define-lambdaLVar-language lambdaLVar-natpair-ivars
    my-lub
    (natural natural)
    (natural Bot)
    (Bot natural))

  ;; my-lub: A function that takes two pairs (they might be of the
  ;; form (natural natural), (natural Bot), or (Bot natural)) and
  ;; returns a pair that is their least upper bound.

  ;; Because they're IVars, we can only safely combine two pairs if
  ;; one of them has only the car filled in, and the other has only
  ;; the cadr filled in -- or if whatever they're filled in with is
  ;; the same.

  ;; assumes that a1 and a2 aren't both numbers, or if they are then
  ;; they're the same
  (define lub-helper
    (lambda (a1 a2)
      (cond
        [(and (number? a1) (number? a2) (equal? a1 a2)) a1]
        [(and (number? a1) (number? a2) (not (equal? a1 a2)))
         ;; If we get here, something's wrong
         (error "oops!")]
        [(number? a1) a1]
        [(number? a2) a2]
        [else 'Bot])))

  (define my-lub
    (lambda (p1 p2)
      (let ([car1 (car p1)]
            [cadr1 (cadr p1)]
            [car2 (car p2)]
            [cadr2 (cadr p2)])
        (cond
          ;; nat/Bot, nat/Bot
          ;; nat/Bot, nat/nat
          ;; nat/nat, nat/Bot
          ;; nat/nat, nat/nat
          [(and (number? car1) (number? car2) (not (equal? car1 car2)))
           'Top]

          ;; Bot/nat, Bot/nat
          ;; nat/nat, Bot/nat
          ;; Bot/nat, nat/nat
          [(and (number? cadr1) (number? cadr2) (not (equal? cadr1 cadr2)))
           'Top]

          ;; nat/Bot, Bot/nat
          ;; Bot/nat, nat/Bot
          [else (list
                 (lub-helper car1 car2)
                 (lub-helper cadr1 cadr2))])))))

(module test-suite racket
  (require redex/reduction-semantics)
  (require (submod ".." language))
  (require srfi/1)
  (require "test-helpers.rkt")

  (provide
   test-fast
   test-all)

  (define (test-fast)
    (display "Running metafunction tests...")
    (flush-output)
    (time (meta-test-suite))

    (display "Running test suite with fast-rr...")
    (flush-output)
    (time (program-test-suite fast-rr))

    (display "Running test suite with slow-rr...")
    (flush-output)
    (time (program-test-suite slow-rr))

    (display "Running slow test suite with fast-rr...")
    (flush-output)
    (time (slow-program-test-suite fast-rr)))

  (define (test-all)
    (test-fast)
    (display "Running slow test suite with slow-rr...")
    (flush-output)
    (time (slow-program-test-suite slow-rr)))

  ;; Test suite
  
  (define (meta-test-suite)

    (test-equal
     (term (incomp ((3 Bot) (Bot 4))))
     (term #f))

    (test-equal
     (term (incomp ((2 Bot) (3 Bot) (Bot 4))))
     (term #f))

    (test-equal
     (term (incomp (Bot (4 Bot))))
     (term #f))

    (test-equal
     (term (incomp ((3 Bot) (4 Bot))))
     (term #t))

    (test-equal
     (term (incomp ((Bot 3) (Bot 4))))
     (term #t))

    (test-equal
     (term (incomp ((Bot 1) (Bot 2) (Bot 3) (Bot 4) (Bot 5))))
     (term #t))

    (test-equal
     (term (incomp ((Bot 1) (Bot 2) (Bot 3) (Bot 4) (Bot 5) (1 Bot))))
     (term #f))

    (test-equal
     (term (exists-d (Bot 1) ()))
     (term #f))

    (test-equal
     (term (exists-d (Bot 6) (Bot)))
     (term Bot))

    (test-equal
     (term (exists-d (Bot 6) ((Bot 9))))
     (term #f))

    (test-equal
     (term (exists-d (Bot 3) ((Bot 3))))
     (term (Bot 3)))

    (test-equal
     (term (exists-d (Bot 6) ((Bot 7) (Bot 8) (Bot 9))))
     (term #f))

    (test-equal
     (term (exists-d (Bot 6) ((Bot 7) (Bot 8) (Bot 9) (Bot 6))))
     (term (Bot 6)))

    (test-equal
     (term (exists-d (Bot 6) ((Bot 7) (Bot 8) (Bot 9) Bot)))
     (term Bot))

    (test-equal
     (term (exists-d (6 6) ((Bot 7) (Bot 8) (Bot 9) (Bot 6))))
     (term (Bot 6)))

    (test-equal
     (term (lub Bot Bot))
     (term Bot))

    (test-equal
     (term (lub Top (Bot 3)))
     (term Top))

    (test-equal
     (term (lub (3 Bot) (Bot 4)))
     (term (3 4)))

    (test-equal
     (term (lub (3 3) (3 3)))
     (term (3 3)))

    (test-equal
     (term (leq (3 3) (3 3)))
     (term #t))

    (test-equal
     (term (leq Top (3 3)))
     (term #f))

    (test-equal
     (term (leq (3 3) Top))
     (term #t))

    (test-equal
     (term (leq Bot (3 3)))
     (term #t))

    (test-equal
     (term (leq (3 3) Bot))
     (term #f))

    (test-equal
     (term (leq Top Bot))
     (term #f))

    (test-equal
     (term (leq Bot Top))
     (term #t))

    (test-equal
     (term (leq (Bot 3) (3 3)))
     (term #t))

    (test-equal
     (term (leq (3 3) (Bot 3)))
     (term #f))

    (test-equal
     (term (leq (3 3) (4 4)))
     (term #f))

    (test-equal
     (term (leq (5 5) (4 4)))
     (term #f))

    (test-equal
     (term (store-dom ((l1 (4 4)) (l2 (5 5)) (l3 Bot))))
     (term (l1 l2 l3)))

    (test-equal
     (stores-equal-modulo-perms?
      (term (lubstore ((l1 (5 5))
                       (l2 (6 6))
                       (l3 (7 7)))
                      ((l2 (6 6))
                       (l4 (9 9)))))
      (term ((l1 (5 5))
             (l3 (7 7))
             (l2 (6 6))
             (l4 (9 9)))))
     #t)

    (test-equal
     (stores-equal-modulo-perms?
      (term (lubstore ((l1 (5 5))
                       (l2 (6 6))
                       (l3 (7 7)))
                      ((l1 (5 5))
                       (l4 (9 9))
                       (l2 (6 6)))))
      (term ((l3 (7 7))
             (l1 (5 5))
             (l4 (9 9))
             (l2 (6 6)))))
     #t)

    (test-equal
     (stores-equal-modulo-perms?
      (term (lubstore ((l1 Bot)
                       (l2 (6 6))
                       (l3 Bot))
                      ((l1 (5 5))
                       (l4 (9 9))
                       (l2 (6 6)))))
      (term ((l3 Bot)
             (l1 (5 5))
             (l4 (9 9))
             (l2 (6 6)))))
     #t)

    (test-equal
     (term (lubstore-helper ((l1 (5 5)))
                            ()
                            l1))
     (term (5 5)))

    (test-equal
     (term (lubstore-helper ((l1 (Bot 6)))
                            ((l1 (6 6)))
                            l1))
     (term (6 6)))

    (test-equal
     (term (lubstore-helper ((l1 (5 5))
                             (l2 (6 6))
                             (l3 (7 7)))
                            ((l2 (6 6))
                             (l4 (9 9)))
                            l2))
     (term (6 6)))

    (test-equal
     (lset= equal?
            (lset-union equal? (term ()) (term ()))
            (term ()))
     #t)

    (test-equal
     (lset= equal?
            (lset-union equal? (term ()) (term (l1)))
            (term (l1)))
     #t)

    (test-equal
     (lset= equal?
            (lset-union equal? (term (l1 l2)) (term (l1 l2 l3)))
            (term (l1 l2 l3)))
     #t)

    (test-equal
     (lset= equal?
            (lset-union equal? (term (l2 l3)) (term (l1 l4)))
            (term (l2 l3 l1 l4)))
     #t)

    (test-equal
     (lset= equal?
            (lset-union equal? (term (l2 l3)) (term (l1 l2 l4)))
            (term (l3 l1 l2 l4)))
     #t)

    (test-equal
     (term (store-lookup ((l (2 2))) l))
     (term (2 2)))

    (test-equal
     (term (store-update () l (4 4)))
     (term ((l (4 4)))))

    (test-equal
     (term (store-update ((l (Bot 4))) l (4 4)))
     (term ((l (4 4)))))

    (test-equal
     (term (store-update () l Bot))
     (term ((l Bot))))

    (test-equal
     (term (valid ()))
     #f)

    (test-equal
     (term (valid ((3 3))))
     #t)

    (test-equal
     (term (valid ((5 5) (6 6) (7 7))))
     #t)

    (test-equal
     (term (store-dom ()))
     (term ()))

    (test-equal
     (term (store-dom ((l (3 3)) (l1 (4 4)))))
     (term (l l1)))

    (test-equal
     (term (store-dom-diff ((l (3 3)) (l1 (4 4)))
                           ((l (4 4)) (l1 (3 3)))))
     (term ()))

    (test-equal
     (term (store-dom-diff ((l (3 3)))
                           ((l (4 4)) (l1 (3 3)))))
     (term ()))

    (test-equal
     (term (store-dom-diff ((l (4 4)) (l1 (3 3)))
                           ((l (3 3)))))
     (term (l1)))

    (test-equal
     (term (store-dom-diff ((l (4 4)))
                           ()))
     (term (l)))

    (test-equal
     (term (rename-locs (((l Bot))
                         (put l ((3 3))))
                        ((l (4 4)))
                        ()))
     (term
      (((l1 Bot))
       (put l1 ((3 3))))))

    (test-equal
     (term (store-top? ()))
     (term #f))

    (test-equal
     (term (store-top? ((l (3 3)) (l1 (4 4)))))
     (term #f))

    (test-equal
     (term (store-top? TopS))
     (term #t))

    (test-equal
     (term (top? Top))
     (term #t))

    (test-equal
     (term (top? Bot))
     (term #f))

    (test-equal
     (term (top? (3 3)))
     (term #f))

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (4 4)) (l1 (3 3))) ())
      '(((l1 (3 3)) (l (4 4))) ()))
     #t)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l1 (3 3)) (l (4 4))) ())
      '(((l1 (3 3)) (l (4 4))) ((3 3))))
     #f)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (4 4)) (l1 (3 3))) ())
      '(((l1 (3 3)) (l (4 4))) ((3 3))))
     #f)

    (test-equal
     (cfgs-equal-modulo-perms?
      '(((l (3 3)) (l1 (4 4))) ())
      '(((l1 (3 3)) (l (4 4))) ()))
     #f)

    (test-equal
     (term (subst l l1 (((l Bot))
                        (put l ((3 3))))))
     (term (((l1 Bot))
            (put l1 ((3 3))))))

    (test-results))

  (define (program-test-suite rr)

    ;; E-App-1
    (test-->> rr
              (term
               (() ;; empty store
                ((lambda (x_1) x_1)
                 ((lambda (x_1) x_1) (lambda (x_2) x_2)))))
              (term
               (()
                (lambda (x_2) x_2))))

    ;; E-App-2
    (test-->> rr
              (term
               (() ;; empty store
                (((lambda (x_1) x_1) (lambda (x_2) x_2))
                 (lambda (x_1) x_1))))
              (term
               (()
                (lambda (x_1) x_1))))

    ;; E-ParApp
    (test-->> rr
              (term
               (() ;; empty store
                (((lambda (x_1) x_1) (lambda (x_2) x_2))
                 ((lambda (x_1) x_1) (lambda (x_2) x_2)))))
              (term
               (()
                (lambda (x_2) x_2))))

    ;; E-Beta
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

    ;; E-New
    (test-->> rr
              (term
               (((l (3 3)))
                new))
              (term
               (((l (3 3)) (l1 Bot))
                l1)))

    (test-->> rr
              (term
               (((l (3 3)) (l1 (4 4)))
                new))
              (term
               (((l (3 3)) (l1 (4 4)) (l2 Bot))
                l2)))

    ;; E-PutVal
    (test-->> rr
              (term
               (((l Bot))
                (put l ((3 3)))))
              (term
               (((l (3 3)))
                ())))

    (test-->> rr
              (term
               (((l (Bot 3)))
                (put l ((3 3)))))
              (term
               (((l (3 3)))
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

    ;; E-Beta + E-New
    (test-->> rr
              (term
               (() ;; empty store
                ((lambda (x) x) new)))
              (term
               (((l Bot))
                l)))

    ;; let + E-New + E-PutVal + E-GetVal
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 (put x_1 ((3 3)))))
                    (let ((x_3 (get x_1 ((Bot 3)))))
                      x_3)))))
              (term
               (((l (3 3)))
                ((Bot 3)))))

    ;; let par + E-New + E-PutVal + E-GetVal
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par ((x_2 (put x_1 ((Bot 3))))
                            (x_3 (put x_1 ((3 Bot)))))
                    (get x_1 ((3 3)))))))
              (term
               (((l (3 3)))
                ((3 3)))))

    ;; Another aspect of E-PutVal's behavior
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 (put x_1 ((5 5)))))
                    ;; This should just take the lub of the old and new
                    ;; values, i.e., (5 5).
                    (let ((x_3 (put x_1 ((Bot 5)))))
                      (get x_1 ((5 5))))))))
              (term
               (((l (5 5)))
                ((5 5)))))

    ;; E-PutValErr
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let ((x_2 (put x_1 (Top))))
                    x_2))))
              (term
               Error))

    (test-->> rr
              #:equiv cfgs-equal-modulo-perms?
              (term
               (()
                (let par ([x_1 new]
                          [x_2 new])
                  (let par ([x_3 (put x_1 ((3 3)))]
                            [x_4 (put x_2 ((4 4)))])
                    (get x_2 ((4 4)))))))

              ;; When we're using slow-rr, we can end up with a store
              ;; of ((l (3 3)) (l1 (4 4))) or a permutation thereof --
              ;; that is, x_1 is allocated first, followed by x_2.
              ;; When we're using fast-rr, we always seem to get the
              ;; allocation in the opposite order.  This is not
              ;; nondeterministic in the sense that the result of
              ;; reading x_2 is always the same, but it ends up at a
              ;; different location in the store.  This is hack to
              ;; account for that.
              (if (equal? rr slow-rr)
                  (term
                   (((l (3 3))
                     (l1 (4 4)))
                    ((4 4))))
                  (term
                   (((l (4 4))
                     (l1 (3 3)))
                    ((4 4)))))
              (term
               (((l (4 4))
                 (l1 (3 3)))
                ((4 4)))))

    ;;let par put and get
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par ((x_2 (put x_1 ((2 2))))
                            (x_3 (get x_1 ((2 2)))))
                    (get x_1 ((2 2)))))))
              (term
               (((l (2 2)))
                ((2 2)))))

    (test-results))

  (define (slow-program-test-suite rr)

    ;; let par + E-New + E-PutVal + E-GetVal + E-GetValBlock
    (test-->> rr
              (term
               (() ;; empty store
                (let ((x_1 new))
                  (let par
                      ;; Gets stuck trying to get (4 4) out of x_1,
                      ;; then unstuck after the other subexpression
                      ;; finishes.
                      ((x_4 (let par ((x_2 (put x_1 ((Bot 4))))
                                      (x_3 (put x_1 (Bot))))
                              (get x_1 ((4 4)))))
                       ;; Eventually puts (4 4) in x_1 after several
                       ;; dummy beta-reductions.
                       (x_5 ((lambda (x_2)
                               ((lambda (x_2)
                                  ((lambda (x_2)
                                     ((lambda (x_2)
                                        ((lambda (x_2)
                                           (put x_1 ((4 4)))) ())) ())) ())) ())) ())))
                    x_4))))
              (term
               (((l (4 4)))
                ((4 4)))))
    
    (test-results)))

(module test-fast racket
  (require (submod ".." test-suite))
  (test-fast))

(module test-all racket
  (require (submod ".." test-suite))
  (test-all))
