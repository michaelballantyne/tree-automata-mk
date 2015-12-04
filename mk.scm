; Scope object.
; Used to determine whether a branch has occured between variable creation
; and unification to allow the set-var-val! optimization in subst-add. Both variables
; and substitutions will contain a scope. When a substitution flows through a
; conde it is assigned a new scope.

; Creates a new scope that is not scope-eq? to any other scope
(define new-scope
  (lambda ()
    (list 'scope)))

; Scope used when variable bindings should always be made in the substitution,
; as in disequality solving and reification. We don't want to set-var-val! a
; variable when checking if a disequality constraint holds!
(define nonlocal-scope
  (list 'non-local-scope))

(define scope-eq? eq?)


; Logic variable object.
; Contains:
;   val - value for variable assigned by unification using set-var-val! optimization.
;           unbound if not yet set or stored in substitution.
;   scope - scope that the variable was created in.
;   idx - unique numeric index for the variable. Used by the trie substitution representation.
; Variable objects are compared by object identity.

; The unique val for variables that have not yet been bound to a value
; or are bound in the substitution
(define unbound (list 'unbound))

(define var
  (let ((counter -1))
    (lambda (scope)
      (set! counter (+ 1 counter))
      (vector unbound scope counter))))

; Vectors are not allowed as terms, so terms that are vectors are variables.
(define var?
  (lambda (x)
    (vector? x)))

(define var-eq? eq?)

(define var-val
  (lambda (x)
    (vector-ref x 0)))

(define set-var-val!
  (lambda (x v)
    (vector-set! x 0 v)))

(define var-scope
  (lambda (x)
    (vector-ref x 1)))

(define var-idx
  (lambda (x)
    (vector-ref x 2)))


; Substitution object.
; Contains:
;   map - mapping of variables to values
;   scope - scope at current program point, for set-var-val! optimization. Updated at conde.
;               Included in the substitution because it is required to fully define the substitution
;               and how it is to be extended.
;
; Implementation of the substitution map depends on the Scheme used, as we need a map. See mk.rkt
; and mk-vicare.scm.

(define subst
  (lambda (mapping scope)
    (cons mapping scope)))

(define subst-map car)

(define subst-scope cdr)

(define subst-length
  (lambda (S)
    (subst-map-length (subst-map S))))

(define subst-with-scope
  (lambda (S new-scope)
    (subst (subst-map S) new-scope)))

(define empty-subst (subst empty-subst-map (new-scope)))

(define subst-add
  (lambda (S x v)
    ; set-var-val! optimization: set the value directly on the variable
    ; object if we haven't branched since its creation
    ; (the scope of the variable and the substitution are the same).
    ; Otherwise extend the substitution mapping.
    (if (scope-eq? (var-scope x) (subst-scope S))
      (begin
        (set-var-val! x v)
        S)
      (subst (subst-map-add (subst-map S) x v) (subst-scope S)))))

(define subst-lookup
  (lambda (u S)
    ; set-var-val! optimization.
    ; Tried checking the scope here to avoid a subst-map-lookup
    ; if it was definitely unbound, but that was slower.
    (if (not (eq? (var-val u) unbound))
      (var-val u)
      (subst-map-lookup u (subst-map S)))))

; Association object.
; Describes an association mapping the lhs to the rhs. Returned by unification
; to describe the associations that were added to the substitution (whose representation
; is opaque) and used to represent disequality constraints.

(define lhs car)

(define rhs cdr)

; Constraint store object.
; Mapping of representative variable to constraint record. Constraints are
; always on the representative element and must be moved / merged when that
; element changes.

; Implementation depends on the Scheme used, as we need a map. See mk.rkt
; and mk-vicare.scm.

(define empty-c (cons 'any-automata '()))

; State object.
; The state is the value that is monadically passed through the search.
; Contains:
;   S - the substitution
;   C - the constraint store

(define state
  (lambda (S C)
    (cons S C)))

(define state-S (lambda (st) (car st)))
(define state-C (lambda (st) (cdr st)))

(define empty-state (state empty-subst empty-C))

(define state-with-scope
  (lambda (st new-scope)
    (state (subst-with-scope (state-S st) new-scope) (state-C st))))

; Unification

(define walk
  (lambda (u S)
    (if (var? u)
      (let ((val (subst-lookup u S)))
        (if (eq? val unbound)
          u
          (walk val S)))
      u)))

(define occurs-check
  (lambda (x v S)
    (let ((v (walk v S)))
      (cond
        ((var? v) (var-eq? v x))
        ((pair? v)
         (or
           (occurs-check x (car v) S)
           (occurs-check x (cdr v) S)))
        (else #f)))))

(define ext-s-check
  (lambda (x v S)
    (cond
      ((occurs-check x v S) (values #f #f))
      (else (values (subst-add S x v) `((,x . ,v)))))))

; Returns as values the extended substitution and a list of associations added
; during the unification, or (values #f #f) if the unification failed.
;
; Right now appends the list of added values from sub-unifications. Alternatively
; could be threaded monadically, which could be faster or slower.
(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) (values s '()))
        ((var? u) (ext-s-check u v s))
        ((var? v) (ext-s-check v u s))
        ((and (pair? u) (pair? v))
         (let-values (((s added-car) (unify (car u) (car v) s)))
           (if s
             (let-values (((s added-cdr) (unify (cdr u) (cdr v) s)))
               (values s (append added-car added-cdr)))
             (values #f #f))))
        ((equal? u v) (values s '()))
        (else (values #f #f))))))

(define unify*
  (lambda (S+ S)
    (unify (map lhs S+) (map rhs S+) S)))


; Search

; Search result types. Names inspired by the plus monad?
(define mzero (lambda () #f))
(define unit (lambda (c) c))
(define choice (lambda (c f) (cons c f)))

(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambda () e))))

(define empty-f (inc (mzero)))

(define-syntax lambdag@
  (syntax-rules ()
    ((_ (st) e) (lambda (st) e))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((c-inf e))
       (cond
         ((not c-inf) e0)
         ((procedure? c-inf)  (let ((f^ c-inf)) e1))
         ((not (and (pair? c-inf)
                 (procedure? (cdr c-inf))))
          (let ((c^ c-inf)) e2))
         (else (let ((c (car c-inf)) (f (cdr c-inf)))
                 e3)))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (st)
       (inc
         (let ((scope (subst-scope (state-S st))))
           (let ((x (var scope)) ...)
             (bind* (g0 st) g ...))))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (inc (bind (f) g)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) g0 g ...)
     (take n
       (inc
         ((fresh (q) g0 g ...
            (lambdag@ (st)
              (let ((st (state-with-scope st nonlocal-scope)))
                (let ((z ((reify q) st)))
                  (choice z empty-f)))))
          empty-state))))
    ((_ n (q0 q1 q ...) g0 g ...)
     (run n (x) (fresh (q0 q1 q ...) g0 g ... (== `(,q0 ,q1 ,q ...) x))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (q0 q ...) g0 g ...) (run #f (q0 q ...) g0 g ...))))

(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f)
         (() '())
         ((f) (take n f))
         ((c) (cons c '()))
         ((c f) (cons c
                  (take (and n (- n 1)) f))))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (st)
       (inc
         (let ((st (state-with-scope st (new-scope))))
           (mplus*
             (bind* (g0 st) g ...)
             (bind* (g1 st) g^ ...) ...)))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0
                    (inc (mplus* e ...))))))

(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (inc (mplus (f) f^)))))))


(define (apply-intersect shape-c st)
  (let ([a (car shape-c)]  ; automaton
        [v (cdr shape-c)]) ; term that is a variable (walked)
    (let ([existing (lookup-c v st)])
      (if (eq? empty-c existing)
        (let ([intersected (intersect-driver a existing)])
          (if (automaton-non-empty intersected)
            (unit (set-c term intersected st))
            (mzero)))
        (unit (set-c term a st))))))

(define (streamify l)
  (if (null? l)
    (mzero)
    (cons (car l) (lambda () (streamify (cdr l))))))

(define shapeo
  (lambda (a t)
    (lambdag@ (st)
       (let ([t (walk t (state-S st))])
         (if (var? t)
           ; intersect
           (apply-intersect (cons a t) st)
           ; unfold. we know enough to resolve the constraint (if the term is atomic), or to
           ; push the constraint down on to sub-elements (if the term is a pair). This second
           ; case results in multiple answers: say x is constrained as (or (a . b) (c . d)), and
           ; x is found to be (y . z). Then we should produce answers (and (y -> a) (z -> b)),
           ; (and (y -> c) (z -> d))
           (let ([mappings ; list of alists (fresh var) -> tree automata to attach. May have dups
                  ((make-unfold var? walk (state-S st)) a t)])
             (if (null? mappings)
               (mzero)
               (streamify (filter (lambda (a) a)
                                  (map (lambda (single)
                                         (and-foldl apply-intersect st single))
                                       mappings))))))))))
; state -> stream
(define (update-constraints pr st)
  (let ([rebound-var (car pr)]
        [new-term    (cdr pr)])
    (let ([old-automaton (lookup-c rebound-var)])
      (if (eq? old-automaton empty-c)
        (unit st)
        ((shapeo old-automaton new-term) (remove-c rebound-var st))))))



(define ==
  (lambda (u v)
    (lambdag@ (st)
      (let-values (((S added) (unify u v (state-S st))))
        (if S
          (foldl
            (lambda (added-el acc)
              (bind acc (lambdag@ (st) (update-constraints added-el st))))
            (unit (state S (state-C st)))
            added)
          (mzero))))))


(define reify (lambda (x) (lambda (y) y)))

; Constraints
; C refers to the constraint store map
; c refers to an individual constraint record


; Requirements for type constraints:
; 1. Must be positive, not negative. not-pairo wouldn't work.
; 2. Each type must have infinitely many possible values to avoid
;      incorrectness in combination with disequality constraints, like:
;      (fresh (x) (booleano x) (=/= x #t) (=/= x #f))
;(define type-constraint
  ;(lambda (type-pred type-id)
    ;(lambda (u)
      ;(lambdag@ (st)
        ;(let ((term (walk u (state-S st))))
          ;(cond
            ;((type-pred term) (unit st))
            ;((var? term)
             ;(let* ((c (lookup-c term st))
                   ;(T (c-T c)))
               ;(cond
                 ;((eq? T type-id) (unit st))
                 ;((not T) (unit (set-c term (c-with-T c type-id) st)))
                 ;(else (mzero)))))
            ;(else (mzero))))))))

;(define symbolo (type-constraint symbol? 'symbolo))
;(define numbero (type-constraint number? 'numbero))

;(define (add-to-D st v d)
  ;(let* ((c (lookup-c v st))
         ;(c^ (c-with-D c (cons d (c-D c)))))
    ;(set-c v c^ st)))

;(define =/=*
  ;(lambda (S+)
    ;(lambdag@ (st)
      ;(let-values (((S added) (unify* S+ (subst-with-scope (state-S st) nonlocal-scope))))
        ;(cond
          ;((not S) (unit st))
          ;((null? added) (mzero))
          ;(else
            ;; Choose one of the disequality elements (el) to attach the constraint to. Only
            ;; need to choose one because all must fail to cause the constraint to fail.
            ;(let ((el (car added)))
              ;(let ((st (add-to-D st (car el) added)))
                ;(if (var? (cdr el))
                  ;(add-to-D st (cdr el) added)
                  ;st)))))))))

;(define =/=
  ;(lambda (u v)
    ;(=/=* `((,u . ,v)))))

;(define absento
  ;(lambda (ground-atom term)
    ;(lambdag@ (st)
      ;(let ((term (walk term (state-S st))))
        ;(cond
          ;((pair? term)
           ;(let ((st^ ((absento ground-atom (car term)) st)))
             ;(and st^ ((absento ground-atom (cdr term)) st^))))
          ;((eqv? term ground-atom) (mzero))
          ;((var? term)
           ;(let* ((c (lookup-c term st))
                  ;(A (c-A c)))
             ;(if (memv ground-atom A)
               ;(unit st)
               ;(let ((c^ (c-with-A c (cons ground-atom A))))
                 ;(unit (set-c term c^ st))))))
          ;(else (unit st)))))))

;; Fold lst with proc and initial value init. If proc ever returns #f,
;; return with #f immediately. Used for applying a series of constraints
;; to a state, failing if any operation fails.
(define (and-foldl proc init lst)
  (if (null? lst)
    init
    (let ([res (proc (car lst) init)])
      (and res (and-foldl proc res (cdr lst))))))

;(define ==
  ;(lambda (u v)
    ;(lambdag@ (st)
      ;(let-values (((S added) (unify u v (state-S st))))
        ;(if S
          ;(and-foldl update-constraints (state S (state-C st)) added)
          ;(mzero))))))


;; Not fully optimized. Could do absento update with fewer hash-refs / hash-sets.
;(define update-constraints
  ;(lambda (a st)
    ;(let ([old-c (lookup-c (lhs a) st)])
      ;(if (eq? old-c empty-c)
        ;st
        ;(let ((st (remove-c (lhs a) st)))
         ;(and-foldl (lambda (op st) (op st)) st
          ;(append
            ;(if (eq? (c-T old-c) 'symbolo)
              ;(list (symbolo (rhs a)))
              ;'())
            ;(if (eq? (c-T old-c) 'numbero)
              ;(list (numbero (rhs a)))
              ;'())
            ;(map (lambda (atom) (absento atom (rhs a))) (c-A old-c))
            ;(map (lambda (d) (=/=* d)) (c-D old-c)))))))))


;; Reification

;(define walk*
  ;(lambda (v S)
    ;(let ((v (walk v S)))
      ;(cond
        ;((var? v) v)
        ;((pair? v)
         ;(cons (walk* (car v) S) (walk* (cdr v) S)))
        ;(else v)))))

;(define vars
  ;(lambda (term acc)
    ;(cond
      ;((var? term) (cons term acc))
      ;((pair? term)
       ;(vars (cdr term) (vars (car term) acc)))
      ;(else acc))))

