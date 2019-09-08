#lang racket/base

(require racket/require
         (for-syntax (subtract-in racket/base syntax/intdef2)
                     racket/match)
         syntax/intdef2
         syntax/parse/define)

(define-syntax (argument stx) (raise-syntax-error #f "cannot be used as an expression" stx))

(define-syntax-parser intdef-lambda
  [(_ body ...+)
   (define intdef (syntax-local-make-internal-definition-context))
   (define arg-ids '())

   (define compile-decl
     (syntax-parser
       #:literals [argument]
       [(argument ~! x:id)
        (syntax-local-internal-definition-context-bind-placeholders! intdef (list #'x))
        (define introduced-x (syntax-local-introduce
                              (internal-definition-context-introduce intdef #'x 'add)))
        (set! arg-ids (cons introduced-x arg-ids))
        #'(begin)]
       [_ #f]))

   (for ([body (in-list (attribute body))])
     (syntax-local-internal-definition-context-extend! intdef
                                                       body
                                                       #:stop-ids (list #'argument)
                                                       #:compile compile-decl))

   (define introduced-arg-ids
     (for/list ([arg-id (in-list arg-ids)])
       (syntax-local-identifier-as-binding (syntax-local-introduce arg-id))))

   (syntax-local-internal-definition-context-finish!
    intdef
    #:wrap (lambda (body-stx)
             (quasisyntax/loc this-syntax
               (lambda #,(reverse introduced-arg-ids)
                 #,body-stx))))])

;; ---------------------------------------------------------------------------------------------------

(define f
  (intdef-lambda
    (argument a)
    (argument b)
    (+ a b)))

(f 3 4)

(define g
  (intdef-lambda
    (argument a)
    (define b (* a 2))
    (argument c)
    (+ b c)))

(g 3 4)

(define h
  (intdef-lambda
    (argument a)
    (define-syntax m
      (begin
        (displayln "evaluating m")
        (syntax-rules () [(_) a])))
    (#%expression (m))))

(h 42)
