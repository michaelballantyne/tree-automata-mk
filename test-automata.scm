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

;(display (run 1 (q) (shapeo env '((a b) (c d)))))
(display (run 1 (q) (shapeo env '((a . b) (c . d)))))
(display "\n")
(display (run 1 (q) (shapeo env '((a . (2 . 3)) (c . 1)))))
(display "\n")
(display (run 1 (q) (shapeo env '((5 . (2 . 3)) (c . 1)))))
(display "\n")
