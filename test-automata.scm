(clear-caches)
(define sym (new-automaton '("sym-empty") (list (make-production 'symbol? '(())))))
(define num (new-automaton '("num-empty") (list (make-production 'number? '(())))))
(define nil (new-automaton '("nil-empty") (list (make-production 'null? '(())))))
(define term1 (new-automaton '("term1-empty")))
(automaton-productions-set!
 term1
 (list (make-production 'pair? (list (list term1 term1)))
       (make-production 'symbol? '(()))
       (make-production 'number? '(()))))
(define binding (new-automaton '("binding-empty")
                               (list (make-production 'pair? (list (list sym term1))))))

(define env (new-automaton '("env-empty")))
(automaton-productions-set!
 env
 (list (make-production 'null? '(()))
       (make-production 'pair?
                        (list (list binding env)))))

;(length (run* (q) (shapeo env '((a b) (c d)))))
(test ""
  (length (run* (q) (shapeo env '((a . b) (c . d)))))
  1)

(test ""
  (length (run* (q) (shapeo env '((a . (2 . 3)) (c . 1)))))
  1)

(test "" (length (run* (q) (shapeo env '((5 . (2 . 3)) (c . 1)))))
  0)

(test "" (length (run* (q)
              (== q '((a . (2 . 3)) (c . 1)))
              (shapeo env q)))
  1)

(test "" (length (run* (q)
              (fresh (a b)
                (== a '(a . (2 . 3)))
                (== b '(c . 1))
                (== q (list a b))
                (shapeo env q))))
  1)

(test "" (length (run* (q)
              (fresh (a b c)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b))
                (shapeo env q))))
  1)

(test "" (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  1)

(test "" (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(2 . 1))
                (== q (list a b)))))
  0)

(test ""
  (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  1)

(test ""
  (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (shapeo num c)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  0)

(test ""
  (length (run* (q)
              (fresh (a b c)
                (shapeo env q)
                (shapeo term1 c)
                (== c '(2 . 3))
                (== a `(a . ,c))
                (== b '(c . 1))
                (== q (list a b)))))
  1)

(display (run* (q) (shapeo env q)))
