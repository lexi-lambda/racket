#lang racket/base

(require racket/require
         (for-syntax (subtract-in racket/base
                                  (for-template syntax/intdef2))
                     syntax/parse
                     syntax/transformer)
         syntax/intdef2)

(provide block)

(define-syntax block
  (make-expression-transformer
   (syntax-parser
     [(_ defn-or-expr ...)
      (define intdef (syntax-local-make-internal-definition-context))
      (for ([defn-or-expr (in-list (attribute defn-or-expr))])
        (syntax-local-internal-definition-context-extend! intdef defn-or-expr))
      (unless (internal-definition-context-ends-in-expression? intdef)
        (syntax-local-internal-definition-context-extend! intdef #'(void)))
      (internal-definition-context-finish! intdef #:context this-syntax)])))
