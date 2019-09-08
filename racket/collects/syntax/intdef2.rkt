#lang racket/base

(require racket/require
         (for-syntax (subtract-in (rename-in racket/base [internal-definition-context?
                                                          primitive-internal-definition-context?])
                                  (for-template "private/intdef2.rkt"))
                     racket/contract/base)
         "private/intdef2.rkt")

(provide (for-syntax primitive-internal-definition-context?))

(begin-for-syntax
  (provide (contract-out
            [internal-definition-context?
             (-> any/c boolean?)]
            [internal-definition-context-empty?
             (-> internal-definition-context? boolean?)]
            [internal-definition-context-ends-in-expression?
             (-> internal-definition-context? boolean?)]
            [internal-definition-context-ends-in-definition?
             (-> internal-definition-context? boolean?)]
            [internal-definition-context->primitive-internal-definition-context
             (-> internal-definition-context? primitive-internal-definition-context?)]
            [internal-definition-context-introduce
             (->* [internal-definition-context? syntax?] [(or/c 'flip 'add 'remove)] syntax?)]
            [syntax-local-make-internal-definition-context
             (->* [] #:pre (syntax-transforming?/precondition) internal-definition-context?)]
            [syntax-local-expand-in-internal-definition-context
             (->* [syntax?
                   internal-definition-context?
                   (listof identifier?)]
                  [#:extra-intdefs (listof internal-definition-context?)
                   #:introduce? any/c]
                  #:pre (syntax-transforming?/precondition)
                  syntax?)]
            [syntax-local-internal-definition-context-extend!
             (->* [internal-definition-context?
                   syntax?]
                  [#:stop-ids (listof identifier?)
                   #:compile (-> syntax? (or/c syntax? #f))
                   #:extra-intdefs (listof internal-definition-context?)
                   #:hidden? any/c
                   #:introduce? any/c]
                  #:pre (syntax-transforming?/precondition)
                  void?)]
            [syntax-local-internal-definition-context-bind-placeholders!
             (->* [internal-definition-context?
                   (listof identifier?)]
                  [#:introduce? any/c]
                  #:pre (syntax-transforming?/precondition)
                  (listof identifier?))]
            [syntax-local-internal-definition-context-finish!
             (->* [internal-definition-context?]
                  [#:context (or/c syntax? #f)
                   #:wrap (-> syntax? syntax?)]
                  #:pre (syntax-transforming?/precondition)
                  syntax?)]
            [syntax-local-value
             (->* [identifier?]
                  [(or/c (-> any) #f)
                   (listof internal-definition-context?)
                   #:immediate? any/c
                   #:introduce? any/c]
                  #:pre (syntax-transforming?/precondition)
                  any)]))

  (define (syntax-transforming?/precondition)
    (or (syntax-transforming?) "not currently expanding")))
