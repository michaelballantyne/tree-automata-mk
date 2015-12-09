#lang racket/base

(require automata-kanren
         rackunit)

(clear-caches!)

(define-automata
    [env [null?] [pair? binding env]]
    [binding [pair? sym term1]]
    [term1 [pair? term1 term1] [symbol?] [number?]]
    [sym [symbol?]]
    [num [number?]]
    [nil [null?]])

;(length (run* (q) (shapeo env '((a b) (c d)))))

(check-equal?
  (length (run* (q) (shapeo env '((a . b) (c . d)))))
  1)

(check-equal?
  (length (run* (q) (shapeo env '((a . (2 . 3)) (c . 1)))))
  1)

(check-equal? (length (run* (q) (shapeo env '((5 . (2 . 3)) (c . 1)))))
  0)

(check-equal? (length (run* (q)
              (== q '((a . (2 . 3)) (c . 1)))
              (shapeo env q)))
  1)

(check-equal? (length (run* (q)
              (fresh (a b)
                (== a '(a . (2 . 3)))
                (== b '(c . 1))
                (== q (list a b))
                (shapeo env q))))
  1)

(check-equal? (length (run* (q)
              (fresh (a b c)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b))
                (shapeo env q))))
  1)

(check-equal? (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  1)

(check-equal? (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(2 . 1))
                (== q (list a b)))))
  0)

(check-equal?
  (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  1)

(check-equal?
  (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (shapeo num c)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  0)

(check-equal?
  (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (shapeo term1 c)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  1)

;(display (run* (q) (shapeo env q)))
