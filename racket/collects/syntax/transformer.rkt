#lang racket/base

(require (for-template racket/base))

(provide make-expression-transformer
         make-variable-like-transformer)

(define (make-expression-transformer transformer)
  (unless (or (procedure? transformer)
              (set!-transformer? transformer))
    (raise-argument-error 'make-expression-transformer
                          "(or/c set!-transformer? procedure?)"
                          transformer))

  (define transformer-name (object-name transformer))
  (define name (if (symbol? transformer-name)
                   transformer-name
                   'expression-transformer))
  (define transformer-proc-value (if (set!-transformer? transformer)
                                     (set!-transformer-procedure transformer)
                                     transformer))
  (define transformer-proc (or (procedure-extract-target transformer-proc-value)
                               transformer-proc-value))

  (procedure-rename
   (lambda (stx)
     (unless (syntax? stx)
       (raise-argument-error name "syntax?" stx))
     (unless (syntax-transforming?)
       (raise-arguments-error name "not currently expanding"))
     (if (eq? (syntax-local-context) 'expression)
         (transformer-proc stx)
         (quasisyntax/loc stx
           (#%expression #,stx))))
   name))

(struct variable-like-transformer [procedure]
  #:property prop:procedure (struct-field-index procedure)
  #:property prop:set!-transformer (struct-field-index procedure))

(define (make-variable-like-transformer ref-stx [set!-handler #f])
  (unless (or (syntax? ref-stx) (procedure? ref-stx))
    (raise-argument-error 'make-variable-like-transformer "(or/c syntax? procedure?)" ref-stx))
  (unless (or (syntax? set!-handler) (procedure? set!-handler) (eq? set!-handler #f))
    (raise-argument-error 'make-variable-like-transformer
                          "(or/c syntax? procedure? #f)"
                          set!-handler))
  (variable-like-transformer
   (lambda (stx)
     (syntax-case stx (set!)
       [id
        (identifier? #'id)
        (cond [(procedure? ref-stx) (ref-stx stx)]
              [else                 ref-stx])]
       [(set! id val)
        (cond [(procedure? set!-handler)
               (set!-handler stx)]
              [(syntax? set!-handler)
               (with-syntax ([setter set!-handler])
                 (syntax/loc stx (setter val)))]
              [else
               (raise-syntax-error #f "cannot mutate identifier" stx #'id)])]
       [(id . args)
        (let ([stx* (cons #'(#%expression id) (cdr (syntax-e stx)))])
          (datum->syntax stx stx* stx))]))))
