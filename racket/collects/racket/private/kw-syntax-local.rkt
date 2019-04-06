(module kw-local-expand "pre-base.rkt"
  (require (prefix-in k: '#%kernel))

  (provide syntax-local-expand-expression)

  (define (syntax-local-expand-expression stx [opaque-only? #f]
                                          #:intdefs [intdefs '()]
                                          #:value-bindings [value-bindings #f])
    (k:syntax-local-expand-expression stx opaque-only? intdefs value-bindings)))
