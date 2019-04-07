#lang racket/base

(require (for-syntax racket/base
                     (prefix-in racket: racket/base)
                     (only-in racket/syntax current-syntax-context)
                     syntax/apply-transformer
                     syntax/kerncase
                     syntax/transformer))

(provide (for-syntax internal-definition-context?
                     internal-definition-context-empty?
                     internal-definition-context-ends-in-expression?
                     internal-definition-context-ends-in-definition?
                     internal-definition-context-sealed?
                     internal-definition-context->primitive-internal-definition-context
                     internal-definition-context-introduce
                     syntax-local-make-internal-definition-context
                     syntax-local-expand-in-internal-definition-context
                     syntax-local-internal-definition-context-extend!
                     syntax-local-internal-definition-context-finish!
                     syntax-local-value)
         #%expression/internal-definition-context
         block/internal-definition-context)

(begin-for-syntax
  ;; -------------------------------------------------------------------------------------------------
  ;; helper functions

  (define make-liberal-define-context
    (let ()
      (struct liberal-define-context ()
        #:property prop:liberal-define-context #t)
      (lambda () (liberal-define-context))))

  (struct opaque-box (value))

  (define (local-apply-transformer/any-result proc stx context intdefs)
    (define expanded-stx (local-apply-transformer
                          (lambda (stx)
                            (define result (proc stx))
                            (if (syntax? result)
                                result
                                (datum->syntax #f (opaque-box result))))
                          stx
                          context
                          intdefs))
    (define expanded-value (syntax-e expanded-stx))
    (if (opaque-box? expanded-value)
        (opaque-box-value expanded-value)
        expanded-stx))

  (define (maybe-stx-dispatch-id stx)
    (syntax-case stx ()
      [x (identifier? #'x) #'x]
      [(x . _) (identifier? #'x) #'x]
      [_ #f]))

  (define maybe-syntax-local-introduce
    (case-lambda
      [(introduce?)
       (if introduce?
           syntax-local-introduce
           (lambda (stx) stx))]
      [(introduce? stx)
       (if introduce?
           (syntax-local-introduce stx)
           stx)]))
  (define maybe-syntax-local-unintroduce
    (case-lambda
      [(introduce?)
       (maybe-syntax-local-introduce (not introduce?))]
      [(introduce? stx)
       (maybe-syntax-local-introduce (not introduce?) stx)]))
  (define (maybe-syntax-local-introduce+unintroduce introduce?)
    (if introduce?
        (values syntax-local-introduce (lambda (stx) stx))
        (values (lambda (stx) stx) syntax-local-introduce)))

  (define (keep-for-track stx #:introduce? introduce?)
    (define dispatch-id (maybe-stx-dispatch-id stx))
    (cons (maybe-syntax-local-introduce introduce? dispatch-id)
          (datum->syntax #f #f stx stx)))

  (define (check-literal-intdef stx #:context context-stx)
    (define val (syntax-e stx))
    (unless (internal-definition-context? stx)
      (raise-syntax-error #f "not a literal internal definition context" context-stx stx))
    val)

  ; Avoid a dependency on syntax/id-set, which brings in a lot of other things.
  (struct bound-id-set (table))
  (define (mutable-bound-id-set)
    (bound-id-set (make-hasheq)))
  (define (bound-id-set-add! s id)
    (hash-update! (bound-id-set-table s)
                  (syntax-e id)
                  (lambda (ids) (if (member id ids bound-identifier=?)
                                    ids
                                    (cons id ids)))
                  '()))
  (define (bound-id-set-member? s id)
    (define ids (hash-ref (bound-id-set-table s) (syntax-e id) #f))
    (and ids (member id ids bound-identifier=?)))

  ;; -------------------------------------------------------------------------------------------------
  ;; core definitions

  (struct internal-definition-context (intdef
                                       [prune-scopes-proc #:mutable]
                                       expand-ctx
                                       bound-ids
                                       [val-bindings #:mutable]
                                       [final-exprs #:mutable]
                                       [ends-in-definition? #:mutable]
                                       [orig-stxs #:mutable]
                                       [disappeared-ids #:mutable]
                                       [track-stxs #:mutable]))

  (define (internal-definition-context-prune-scopes intdef stx)
    ((internal-definition-context-prune-scopes-proc intdef) stx))

  (define (internal-definition-context-prune-from! intdef pruned-intdef)
    (define old-prune-scopes-proc (internal-definition-context-prune-scopes-proc intdef))
    (set-internal-definition-context-prune-scopes-proc!
     intdef
     (lambda (stx)
       (old-prune-scopes-proc (internal-definition-context-introduce pruned-intdef stx 'remove)))))

  (define (internal-definition-context-add-expr! intdef stx #:introduce? introduce?)
    (define prev-exprs (internal-definition-context-final-exprs intdef))
    (define flipped-stx (maybe-syntax-local-introduce introduce? stx))
    (set-internal-definition-context-final-exprs! intdef (cons flipped-stx prev-exprs))
    (set-internal-definition-context-ends-in-definition?! intdef #f))

  (define (internal-definition-context-add-orig-stx! intdef stx)
    (set-internal-definition-context-orig-stxs!
     intdef (cons stx (internal-definition-context-orig-stxs intdef))))

  (define (internal-definition-context-add-track-stx! intdef stx #:introduce? introduce?)
    (set-internal-definition-context-track-stxs!
     intdef (cons (keep-for-track stx #:introduce? introduce?)
                  (internal-definition-context-track-stxs intdef))))

  ;; -------------------------------------------------------------------------------------------------
  ;; public API

  (define (syntax-local-make-internal-definition-context)
    (internal-definition-context (racket:syntax-local-make-definition-context)
                                 (lambda (stx) stx)
                                 (list (make-liberal-define-context))
                                 (mutable-bound-id-set)
                                 '() '() #f '() '() '()))

  (define (internal-definition-context-empty? intdef)
    (and (not (internal-definition-context-ends-in-definition? intdef))
         (null? (internal-definition-context-final-exprs intdef))))

  (define (internal-definition-context-ends-in-expression? intdef)
    (not (null? (internal-definition-context-final-exprs intdef))))

  (define (internal-definition-context-sealed? intdef)
    (racket:internal-definition-context-sealed? (internal-definition-context-intdef intdef)))

  (define (internal-definition-context->primitive-internal-definition-context intdef)
    (internal-definition-context-intdef intdef))

  (define (internal-definition-context-introduce intdef id [mode 'flip])
    (racket:internal-definition-context-introduce
     (internal-definition-context-intdef intdef) id mode))

  (define (syntax-local-value id-stx [failure-thunk #f] [intdefs '()]
                              #:immediate? [immediate? #f]
                              #:introduce? [introduce? #t])
    (define r:intdefs (map internal-definition-context-intdef intdefs))
    (define unintroduced-stx (maybe-syntax-local-unintroduce introduce? id-stx))
    (cond
      [immediate?
       (define-values [value target]
         (racket:syntax-local-value/immediate unintroduced-stx failure-thunk r:intdefs))
       value]
      [else
       (racket:syntax-local-value unintroduced-stx failure-thunk r:intdefs)]))

  (define (syntax-local-internal-definition-context-bind! intdef ids rhs
                                                          #:syntaxes? syntaxes?
                                                          #:extra-intdefs [extra-intdefs '()]
                                                          #:introduce? [introduce? #t])
    (define-values [maybe-introduce maybe-unintroduce]
      (maybe-syntax-local-introduce+unintroduce introduce?))

    (define bound-ids (internal-definition-context-bound-ids intdef))
    (define intdef-ids
      (for/list ([id (in-list ids)])
        (define pre-id (syntax-local-identifier-as-binding (maybe-introduce id)))
        (define intdef-id (internal-definition-context-introduce intdef pre-id 'add))
        (when (bound-id-set-member? bound-ids intdef-id)
          (raise-syntax-error #f "duplicate binding name" id))
        intdef-id))

    (syntax-local-bind-syntaxes (map maybe-unintroduce ids)
                                (and syntaxes? (maybe-unintroduce rhs))
                                (internal-definition-context-intdef intdef)
                                (map internal-definition-context-intdef extra-intdefs))

    (for ([intdef-id (in-list intdef-ids)])
      (bound-id-set-add! bound-ids intdef-id))
    (set-internal-definition-context-ends-in-definition?! intdef #t)

    (cond
      [syntaxes?
       (set-internal-definition-context-disappeared-ids!
        intdef (append intdef-ids (internal-definition-context-disappeared-ids intdef)))]
      [else
       (define old-val-bindings (internal-definition-context-val-bindings intdef))
       (define new-val-binding (cons intdef-ids (maybe-introduce rhs)))
       (define exprs (internal-definition-context-final-exprs intdef))
       (define all-val-bindings
         (cond
           [(null? exprs)
            (cons new-val-binding old-val-bindings)]
           [else
            (set-internal-definition-context-final-exprs! intdef '())
            (define intermediate-exprs-binding (cons '() #`(begin #,@exprs (values))))
            (cons new-val-binding (cons intermediate-exprs-binding old-val-bindings))]))
       (set-internal-definition-context-val-bindings! intdef all-val-bindings)]))

  (define (syntax-local-expand-in-internal-definition-context stx intdef stop-ids
                                                              #:extra-intdefs [extra-intdefs '()]
                                                              #:introduce? [introduce? #t])
    (local-expand (maybe-syntax-local-unintroduce introduce? stx)
                  (internal-definition-context-expand-ctx intdef)
                  stop-ids
                  (cons (internal-definition-context-intdef intdef)
                        (map internal-definition-context-intdef extra-intdefs))))

  (define (syntax-local-internal-definition-context-extend! intdef stx
                                                            #:stop-ids [stop-ids '()]
                                                            #:compile [compile-proc (lambda (stx) #f)]
                                                            #:extra-intdefs [extra-intdefs '()]
                                                            #:hidden? [hidden? #f]
                                                            #:introduce? [introduce? #t])
    (define-values [maybe-introduce maybe-unintroduce]
      (maybe-syntax-local-introduce+unintroduce introduce?))

    (define r:intdef (internal-definition-context-intdef intdef))
    (define r:extra-intdefs (map internal-definition-context-intdef extra-intdefs))
    (define expand-ctx (internal-definition-context-expand-ctx intdef))
    (define (prune-scopes stx) (internal-definition-context-prune-scopes intdef stx))

    (define extra-stop-ids
      (for/lists (seen)
                 ([stop-id (in-list stop-ids)]
                  #:unless (member stop-id (kernel-form-identifier-list) free-identifier=?)
                  #:unless (member stop-id seen free-identifier=?))
        stop-id))
    (define all-stop-ids (append extra-stop-ids (kernel-form-identifier-list)))

    (unless hidden?
      (internal-definition-context-add-orig-stx! intdef (maybe-introduce stx)))

    (let loop ([stxs (list stx)]
               [current-stop-ids all-stop-ids])
      (unless (null? stxs)
        (define expanded-stx
          (syntax-local-expand-in-internal-definition-context (car stxs) intdef current-stop-ids
                                                              #:extra-intdefs extra-intdefs
                                                              #:introduce? introduce?))
        (define disarmed-stx (syntax-disarm expanded-stx #f))
        (define maybe-dispatch-id (maybe-stx-dispatch-id disarmed-stx))

        (define (handle-core-form introduced-dispatch-id)
          (cond
            ;; begin
            [(free-identifier=? introduced-dispatch-id #'begin)
             (syntax-case disarmed-stx ()
               [(_ form ...)
                (loop (append (for/list ([form (in-list (syntax->list #'(form ...)))])
                                (syntax-track-origin form
                                                     disarmed-stx
                                                     introduced-dispatch-id))
                              (cdr stxs))
                      all-stop-ids)])]

            ;; define-values / define-syntaxes
            [(or (and (free-identifier=? introduced-dispatch-id #'define-values)
                      (box-immutable #f))
                 (and (free-identifier=? introduced-dispatch-id #'define-syntaxes)
                      (box-immutable #t)))
             => (lambda (stxs?-box)
                  (define stxs? (unbox stxs?-box))
                  (syntax-case disarmed-stx ()
                    [(_ (id ...) rhs)
                     (let ([ids (syntax->list #'(id ...))])
                       (for ([id (in-list ids)])
                         (unless (identifier? id)
                           (raise-syntax-error #f "not an identifier" expanded-stx id)))
                       (define pruned-ids (map prune-scopes ids))
                       (syntax-local-internal-definition-context-bind! intdef
                                                                       pruned-ids
                                                                       #'rhs
                                                                       #:syntaxes? stxs?
                                                                       #:extra-intdefs extra-intdefs
                                                                       #:introduce? introduce?)
                       (internal-definition-context-add-track-stx! intdef disarmed-stx
                                                                   #:introduce? introduce?)
                       (loop (cdr stxs) all-stop-ids))]
                    [(_ _)
                     (raise-syntax-error #f "missing expression after identifiers" expanded-stx)]
                    [(_ ids _)
                     (raise-syntax-error #f "not a list of identifiers" expanded-stx #'ids)]
                    [(_ _ rhs ...)
                     (raise-syntax-error #f
                                         "multiple expressions after identifiers"
                                         expanded-stx
                                         #f
                                         (syntax->list #'(rhs ...)))]))]

            ;; other non-expressions
            [(member introduced-dispatch-id
                     (list #'#%provide #'#%declare #'module*)
                     free-identifier=?)
             (raise-syntax-error #f "only allowed at module top level" expanded-stx)]
            [(member introduced-dispatch-id
                     (list #'#%require #'module #'begin-for-syntax)
                     free-identifier=?)
             (raise-syntax-error #f "only allowed at module top level or top level" expanded-stx)]

            ;; expressions
            [else
             (handle-expression)]))

        (define (handle-expression)
          (internal-definition-context-add-expr! intdef expanded-stx #:introduce? introduce?)
          (loop (cdr stxs) all-stop-ids))

        (cond
          ;; try compile
          [(local-apply-transformer/any-result compile-proc
                                               (maybe-unintroduce disarmed-stx)
                                               expand-ctx
                                               (cons r:intdef r:extra-intdefs))
           => (lambda (compiled-stx)
                (define tracked-stx
                  (if maybe-dispatch-id
                      (syntax-track-origin compiled-stx
                                           disarmed-stx
                                           (maybe-introduce maybe-dispatch-id))
                      compiled-stx))
                (loop (cons (syntax-rearm tracked-stx expanded-stx #t) (cdr stxs))
                      all-stop-ids))]

          ;; stopped on identifier
          [maybe-dispatch-id
           (define introduced-dispatch-id (maybe-introduce maybe-dispatch-id))
           (if (member introduced-dispatch-id extra-stop-ids)
               ; stopped on extra stop id that wasn’t handled by compile,
               ; try again without the stop id
               (loop (cons expanded-stx (cdr stxs))
                     (remove introduced-dispatch-id all-stop-ids free-identifier=?))
               ; otherwise, this must be a core form
               (handle-core-form introduced-dispatch-id))]

          ;; other expressions
          [else
           (handle-expression)]))))

  (define (syntax-local-internal-definition-context-finish!
           intdef
           #:context [context-stx (current-syntax-context)])
    (define body-exprs (internal-definition-context-final-exprs intdef))

    (define last-was-defn? (internal-definition-context-ends-in-definition? intdef))
    (when (or last-was-defn? (null? body-exprs))
      (define orig-stxs (reverse (internal-definition-context-orig-stxs intdef)))
      (raise-syntax-error (if context-stx
                              #f
                              '|begin (possibly implicit)|)
                          (if last-was-defn?
                              "no expression after a sequence of internal definitions"
                              "expected at least one expression")
                          (or context-stx
                              (datum->syntax #f (cons 'begin orig-stxs)))
                          #f
                          orig-stxs))

    (define body-expr #`(begin #,@(map syntax-local-introduce (reverse body-exprs))))
    (define val-bindings (reverse (internal-definition-context-val-bindings intdef)))
    (define introduced-val-bindings (for/list ([val-binding (in-list val-bindings)])
                                      (cons (map syntax-local-introduce (car val-binding))
                                            (syntax-local-introduce (cdr val-binding)))))

    (define-values [ignored opaque-stx]
      (syntax-local-expand-expression body-expr #t
                                      #:intdefs (list (internal-definition-context-intdef intdef))
                                      #:value-bindings introduced-val-bindings))

    (define tracked-stx
      (for/fold ([result-stx opaque-stx])
                ([track-stx (in-list (internal-definition-context-track-stxs intdef))])
        (syntax-track-origin result-stx (cdr track-stx) (car track-stx))))
    (define old-disappeared-bindings (syntax-property tracked-stx 'disappeared-binding))
    (define new-disappeared-bindings (internal-definition-context-disappeared-ids intdef))
    (syntax-property tracked-stx 'disappeared-binding (if old-disappeared-bindings
                                                          (cons new-disappeared-bindings
                                                                old-disappeared-bindings)
                                                          new-disappeared-bindings))))

(define-syntax #%expression/internal-definition-context
  (make-expression-transformer
   (lambda (stx)
     (syntax-case stx ()
       [(_ intdef-stx)
        (let ([intdef (check-literal-intdef #'intdef-stx #:context stx)])
          (syntax-local-internal-definition-context-finish! intdef #:context stx))]))))

(define-syntax block/internal-definition-context
  (make-expression-transformer
   (lambda (stx)
     (syntax-case stx ()
       [(_ intdef-stx defn-or-expr ...)
        (let ()
          (define intdef (check-literal-intdef #'intdef-stx #:context stx))
          (define local-intdef (syntax-local-make-internal-definition-context))
          (internal-definition-context-prune-from! intdef local-intdef)
          (define (bind-redirect stx)
            (syntax-case stx ()
              [(define-id [x ...] _)
               (and (member #'define-id (list #'define-values #'define-syntaxes) free-identifier=?)
                    (andmap identifier? (syntax->list #'[x ...])))
               (begin
                 (unless (null? (syntax->list #'[x ...]))
                   (syntax-local-internal-definition-context-extend!
                    intdef
                    #'(define-syntaxes [x ...]
                        (values (make-rename-transformer (quote-syntax x)) ...))))
                 #f)]
              [_
               #f]))
          (for ([defn-or-expr (in-list (syntax->list #'[defn-or-expr ...]))])
            (syntax-local-internal-definition-context-extend! local-intdef defn-or-expr
                                                              #:compile bind-redirect
                                                              #:extra-intdefs (list intdef)))
          (syntax-local-internal-definition-context-finish! local-intdef #:context stx))]))))
