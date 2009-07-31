#lang s-exp "lang.ss"

(require "munge-ids.ss")
(require "elim-anon.ss")

;; unbox-ids: s-expr (listof symbol) -> s-expr
;; consumes a symbolic expression and a list of identifiers to unbox
;; returns the symbolic expression with each instance of the identifier wrapped in an unbox
(define (unbox-ids ids)
  (lambda (expr)
    (cond
      [(symbol? expr) (if (member expr ids)
                          (list 'unbox expr)
                          expr)]
      [(cons? expr) (map (unbox-ids ids) expr)]
      [else expr])))

;; box-locals: s-expr -> s-expr
;; consumes a symbolic expression
;; returns a symantically equivalent expression with local value definitions
;;    created using set-box!
(define (box-locals expr)
  (cond
    [(cons? expr)
     (cond
       [(equal? (first expr) 'local)
        (local [(define sugared-defs (map ensugar (second expr)))
                (define old-val-defs
                  (filter (lambda (def) (not (cons? (second def)))) sugared-defs))
                (define val-ids (map second old-val-defs))
                (define boxed-val-defs (map box-locals old-val-defs))
                (define old-fun-defs
                  (filter (lambda (def) (cons? (second def))) sugared-defs))
                (define boxed-fun-defs ((unbox-ids val-ids) (map box-locals old-fun-defs)))]
          (list 'local
                (append boxed-fun-defs
                        (map (lambda (symb) (list 'define symb '(box 'undefined))) val-ids))
                (if (empty? boxed-val-defs)
                    (box-locals (third expr))
                    (cons 'begin
                          (foldr (lambda (def rest-box-sets)
                                   (cons (list 'set-box!
                                               (second def)
                                               ((unbox-ids val-ids) (third def)))
                                         rest-box-sets))
                                 (list ((unbox-ids val-ids) (box-locals (third expr))))
                                 boxed-val-defs)))))]
       [else (map box-locals expr)])]
    [else expr]))

;; ready-anormalize: s-expr -> s-expr
(define (ready-anormalize expr)
  (box-locals (elim-anon (munge-identifiers expr))))

(provide ready-anormalize)
