#lang racket/base

(require automata-kanren
         rackunit
         automata-kanren/numbers)

(clear-caches!)

(define-automata
  [env [null?] [pair? binding env]]
  [binding [pair? sym term1]]
  [term1 [pair? term1 term1] [symbol?] [number?]]
  [sym [symbol?]]
  [num [number?]]
  [nil [null?]])


(check-equal?
  (run* (q) (shapeo env '((a . b) (c . d))))
  '(_.0))

(check-equal?
  (run* (q) (shapeo env '((a . (2 . 3)) (c . 1))))
  '(_.0))

(check-equal?
  (run* (q) (shapeo env '((5 . (2 . 3)) (c . 1))))
  '())

(check-equal?
  (run* (q)
    (== q '((a . (2 . 3)) (c . 1)))
    (shapeo env q))
  '(((a . (2 . 3)) (c . 1))))

(check-equal?
  (run* (q)
    (fresh (a b)
      (== a '(a . (2 . 3)))
      (== b '(c . 1))
      (== q (list a b))
      (shapeo env q)))
  '(((a 2 . 3) (c . 1))))

(check-equal?
  (run* (q)
    (fresh (a b c)
      (== c '(2 . 3))
      (== a `(a . ,c))
      (== b '(c . 1))
      (== q (list a b))
      (shapeo env q)))
  '(((a 2 . 3) (c . 1))))

(check-equal?
  (run* (q)
    (fresh (a b c)
      (shapeo env q)
      (== c '(2 . 3))
      (== a `(a . ,c))
      (== b '(c . 1))
      (== q (list a b))))
  '(((a 2 . 3) (c . 1))))

(check-equal?
  (run* (q)
    (fresh (a b c)
      (shapeo env q)
      (== c '(2 . 3))
      (== a `(a . ,c))
      (== b '(2 . 1))
      (== q (list a b))))
  '())

(check-equal?
  (run* (q)
    (fresh (a b c)
      (shapeo env q)
      (== c '(2 . 3))
      (== a `(a . ,c))
      (== b '(c . 1))
      (== q (list a b))))
  '(((a 2 . 3) (c . 1))))

(check-equal?
  (run* (q)
    (fresh (a b c)
      (shapeo env q)
      (shapeo num c)
      (== c '(2 . 3))
      (== a `(a . ,c))
      (== b '(c . 1))
      (== q (list a b))))
  '())

(check-equal?
  (run* (q)
    (fresh (a b c)
      (shapeo env q)
      (shapeo term1 c)
      (== c '(2 . 3))
      (== a `(a . ,c))
      (== b '(c . 1))
      (== q (list a b))))
  '(((a 2 . 3) (c . 1))))

(check-equal?
  (run* (q) (shapeo env q))
  '((_.0 (shapeo (_.0 (env))))))



(check-equal?
  (run* (t)
    (expo '(1 1) '(1 0 1) t))
  (list `(1 1 0 0 1 1 1 1)))

(check-equal?
  (run* (r)
    (logo '(0 1 1 1) '(0 1) '(1 1) r))
  (list `(0 1 1)))
