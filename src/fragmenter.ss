#lang s-exp "lang.ss"

;(require "lift-locals.ss")
(require "anormalize.ss")

(define frag-prepend "f")
(define statement-name 'statement)

(define-struct finfo (return fragments gensym))

;; split-def-list: (listof s-expr) -> (listof (listof s-expr))
;; consumes a list of definitions
;; returns a list containing two lists of definitions
;;    where the first is the beginning of the first list
;;    up to the first value definition that isn't boxing junk
;;    and the second list is the rest of the definitions
(define (split-def-list def-list)
  (cond
    [(empty? def-list) '(() ())]
    [(cons? def-list)
     (if (not (and (cons? (first def-list))
                   (equal? (first (first def-list)) 'define)))
         (error 'split-def-list "expected list of definitions, found something else")
         (if (or (cons? (second (first def-list)))
                 (equal? (third (first def-list)) '(box 'undefined)))
             (local [(define rec-return (split-def-list (rest def-list)))]
               (list (cons (first def-list) (first rec-return))
                     (second rec-return)))
             (list empty def-list)))]))

;; fragment-help: s-expr number -> linfo
;; consumes a symbolic expression and a gensym counter
;; returns a fragmented symbolic expression
(define (fragment-help expr args name gensym frag-locals?)
  (cond
    [(cons? expr)
     (cond
       [(equal? (first expr) 'local)
        (local [(define definitions (if frag-locals?
                                        (foldr (lambda (statement rest-statements)
                                                 (append (get-fragments statement)
                                                         rest-statements))
                                               empty
                                               (second expr))
                                        (second expr)))
                (define split-defs (split-def-list definitions))
                (define new-bound-ids (map (lambda (def) (if (cons? (second def))
                                                         (first (second def))
                                                         (second def)))
                                       (first split-defs)))
                #;(define first-def-id (if (cons? (second (first definitions)))
                                         (first (second (first definitions)))
                                         (second (first definitions))))
                (define rec-rest
                  (if (empty? (second split-defs))
                      (fragment-help (third expr)
                                     (append new-bound-ids args)
                                     name
                                     gensym
                                     true)
                      (fragment-help (list 'define
                                           (cons (string->symbol
                                                  (string-append frag-prepend
                                                                 (number->string gensym)
                                                                 "_"
                                                                 (symbol->string name)))
                                                 (append new-bound-ids
                                                         (cons (second
                                                                (first
                                                                 (second split-defs)))
                                                               args)))
                                       (if (empty? (rest (second split-defs)))
                                           (third expr)
                                           (list 'local
                                                 (rest (second split-defs))
                                                 (third expr))))
                                 args
                                 name
                                 (add1 gensym)
                                 false)))
                (define more-fragments?
                  (and (cons? (finfo-return rec-rest))
                       (equal? (first (finfo-return rec-rest)) 'define)))]
          (make-finfo (list 'local
                            (if (empty? (second split-defs))
                                (first split-defs)
                                (append (first split-defs)
                                        (list (first (second split-defs)))))
                            (if more-fragments?
                                (second (finfo-return rec-rest))
                                (finfo-return rec-rest)))
                      (if more-fragments?
                          (cons (finfo-return rec-rest)
                                (finfo-fragments rec-rest))
                          (finfo-fragments rec-rest))
                      (finfo-gensym rec-rest)))]
       [(equal? (first expr) 'begin)
        (local [(define first-expr (fragment-help (second expr) args name gensym true))
                (define rec-rest
                  (fragment-help (list 'define
                                       (cons (string->symbol
                                              (string-append frag-prepend
                                                             (number->string gensym)
                                                             "_"
                                                             (symbol->string name)))
                                             args)
                                       (if (empty? (rest (rest (rest expr))))
                                           (third expr)
                                           (cons 'begin
                                                 (rest (rest expr)))))
                                 args
                                 name
                                 (add1 gensym)
                                 true))
                (define more-fragments?
                  (and (cons? (finfo-return rec-rest))
                       (equal? (first (finfo-return rec-rest)) 'define)))]
          (make-finfo (list 'begin
                            (finfo-return first-expr)
                            (if more-fragments?
                                (second (finfo-return rec-rest))
                                (finfo-return rec-rest)))
                      (if more-fragments?
                          (cons (finfo-return rec-rest)
                                (finfo-fragments rec-rest))
                          (finfo-fragments rec-rest))
                      (finfo-gensym rec-rest)))]
       [(equal? (first expr) 'set-box!)
        (local [(define fragmented-body
                  (fragment-help (third expr) args (second expr) gensym true))]
          (make-finfo (list 'set-box!
                            (second expr)
                            (finfo-return fragmented-body))
                      (finfo-fragments fragmented-body)
                      (finfo-gensym fragmented-body)))]
       [(equal? (first expr) 'quote) (make-finfo expr empty gensym)]
       [(equal? (first expr) 'define)
        (local [(define filtered-args
                  (if (cons? (second expr))
                      (append (rest (second expr))
                              (filter (lambda (elt)
                                        (not (member elt (rest (second expr)))))
                                      args))
                      args))
                (define rec-rest (fragment-help (third expr)
                                                filtered-args
                                                name
                                                gensym
                                                frag-locals?))]
          (make-finfo (list 'define
                            (second expr)
                            (finfo-return rec-rest))
                      (finfo-fragments rec-rest)
                      (finfo-gensym rec-rest)))]
       [else (foldr (lambda (an-expr rest-info)
                      (local [(define rec-info
                                (fragment-help an-expr
                                               args
                                               name
                                               (finfo-gensym rest-info)
                                               true))]
                        (make-finfo (cons (finfo-return rec-info)
                                          (finfo-return rest-info))
                                    (append (finfo-fragments rec-info)
                                            (finfo-fragments rest-info))
                                    (finfo-gensym rec-info))))
                    (make-finfo empty empty gensym)
                    expr)])]
    [else (make-finfo expr empty gensym)]))

;; get-fragments: s-expr -> (listof s-expr)
;; consumes a toplevel symbolic expression that is the output of anormalize
;; fragments the expression into mini-methods
(define (get-fragments expr)
  (local [(define name (if (and (cons? expr)
                                (or (equal? (first expr) 'define)
                                    (equal? (first expr) 'set-box!)))
                           (if (equal? (first expr) 'define)
                               (if (cons? (second expr))
                                   (first (second expr))
                                   (second expr))
                               (second expr))
                           statement-name))
          (define frag-info (fragment-help expr empty name 0 true))]
    (reverse (cons (finfo-return frag-info)
                   (finfo-fragments frag-info)))))

;; fragment: (listof s-expr) -> (listof s-expr)
;; consumes a toplevel list of symbolic expressions representing a program
;; returns the program with each statement fragmented
(define (fragment program)
  (foldr (lambda (statement rest-statements)
           (append (get-fragments statement) rest-statements))
         empty
         (anormalize program)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; STORAGE

#|
        ;(begin
          #;(printf "in local\n")

                  ;(begin
                    #;(printf "calling fragment-help (~a) on\n ~a\n"
                            frag-locals?
                            (list 'define
                                  (list* (string->symbol
                                          (string-append frag-prepend
                                                         (number->string gensym)
                                                         "_"
                                                         (symbol->string name)))
                                         first-def-id
                                         args)
                                  (if (empty? (rest definitions))
                                      (third expr)
                                      (list 'local
                                            (rest definitions)
                                            (third expr)))))

          ;(begin
            #;(printf "In a local statement, name '~a', args is\n ~a\n"
                    name
                    args)

        ;(begin
          #;(printf "in define: ~a\n"
                  (if (cons? (second expr))
                      (first (second expr))
                      (second expr)))

          ;(begin
            #;(printf "In define, new name is '~a'\n";, returning\n ~a\n"
                    (if (cons? (second expr))
                        (first (second expr))
                        (second expr))
                    #;(list 'define
                          (second expr)
                          (finfo-return rec-rest)))

        ;(begin
          #;(printf "in else: ~a\n"
                  (first expr))
|#