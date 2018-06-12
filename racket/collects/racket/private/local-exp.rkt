(module local-exp '#%kernel
  (#%require "pre-base.rkt")
  (provide lexp)
  (define (lexp stx ctx stop [intdef #f] #:extend-stop-list? [extend? #t])
    (local-expand stx ctx (if (or (not stop) extend?) stop (cons 'only stop)) intdef))
  )
           
