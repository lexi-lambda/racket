#lang racket/base

(require (for-syntax racket/base
                     (prefix-in racket: racket/base)
                     (only-in racket/syntax current-syntax-context)
                     syntax/apply-transformer
                     syntax/kerncase))

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
                     syntax-local-internal-definition-context-bind-placeholders!
                     syntax-local-internal-definition-context-finish!
                     syntax-local-value))

(begin-for-syntax
  ;; -------------------------------------------------------------------------------------------------
  ;; helper functions

  (define intdef-inspector (variable-reference->module-declaration-inspector (#%variable-reference)))
  (define (intdef-syntax-arm stx [use-mode? #f])
    (syntax-arm stx intdef-inspector use-mode?))

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
    (unless (internal-definition-context? val)
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
                                       expand-ctx
                                       bound-ids
                                       [placeholder-ids #:mutable]
                                       [val-bindings #:mutable]
                                       [final-exprs #:mutable]
                                       [ends-in-definition? #:mutable]
                                       [orig-stxs #:mutable]
                                       [disappeared-ids #:mutable]
                                       [track-stxs #:mutable]))

  (define (internal-definition-context-identifiers-as-bindings intdef ids #:introduce? introduce?)
    (define maybe-introduce (maybe-syntax-local-introduce introduce?))
    (define bound-ids (internal-definition-context-bound-ids intdef))
    (for/list ([id (in-list ids)])
      (define pre-id (syntax-local-identifier-as-binding (maybe-introduce id)))
      (define intdef-id (internal-definition-context-introduce intdef pre-id 'add))
      (when (bound-id-set-member? bound-ids intdef-id)
        (raise-syntax-error #f "duplicate binding name" id))
      intdef-id))

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
                                 (list (make-liberal-define-context))
                                 (mutable-bound-id-set)
                                 '() '() '() #f '() '() '()))

  (define (internal-definition-context-empty? intdef)
    (and (not (internal-definition-context-ends-in-definition? intdef))
         (null? (internal-definition-context-final-exprs intdef))))

  (define (internal-definition-context-ends-in-expression? intdef)
    (not (null? (internal-definition-context-final-exprs intdef))))

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

    (define intdef-ids (internal-definition-context-identifiers-as-bindings intdef ids
                                                                            #:introduce? introduce?))
    (syntax-local-bind-syntaxes (map syntax-local-introduce intdef-ids)
                                (and syntaxes? (maybe-unintroduce rhs))
                                (internal-definition-context-intdef intdef)
                                (map internal-definition-context-intdef extra-intdefs))

    (define bound-ids (internal-definition-context-bound-ids intdef))
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

  (define (syntax-local-internal-definition-context-bind-placeholders!
           intdef ids #:introduce? [introduce? #t])
    (define intdef-ids (internal-definition-context-identifiers-as-bindings intdef ids
                                                                            #:introduce? introduce?))
    (syntax-local-bind-syntaxes (map syntax-local-introduce intdef-ids)
                                #f
                                (internal-definition-context-intdef intdef))

    (define bound-ids (internal-definition-context-bound-ids intdef))
    (for ([intdef-id (in-list intdef-ids)])
      (bound-id-set-add! bound-ids intdef-id))

    (define placeholder-ids (internal-definition-context-placeholder-ids intdef))
    (set-internal-definition-context-placeholder-ids! intdef (append intdef-ids placeholder-ids))
    (map (maybe-syntax-local-introduce introduce?) intdef-ids))

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
                       (syntax-local-internal-definition-context-bind! intdef
                                                                       ids
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

  (struct shadowable-placeholder-transformer (intdef target)
    #:property prop:rename-transformer
    (lambda (self)
      (define target (shadowable-placeholder-transformer-target self))
      (define local-target (syntax-local-get-shadower target #t))
      (define pruned-target
        (if (free-identifier=? target local-target)
            ; If the local binding is the definition context binding, we’ll end up in an infinite
            ; loop, so remove the intdef scope. If the resulting identifier is unbound, that’s fine,
            ; since the unbound identifier error will get reported. If it is bound (in a less nested
            ; scope), that’s fine, too, as referencing that binding is okay.
            ;
            ; We only want to do this if the local binding wasn’t shadowed, however, as a more nested
            ; binding might have the intdef scope, and we want to use that if it exists.
            (internal-definition-context-introduce (shadowable-placeholder-transformer-intdef self)
                                                   local-target
                                                   'remove)
            local-target))
      (syntax-property pruned-target 'not-free-identifier=? #t)))

  (define (syntax-local-internal-definition-context-finish!
           intdef
           #:context [context-stx (current-syntax-context)]
           #:wrap [wrap-body values])
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

    ;; rewrite placeholders to refer to shadowing bindings
    (define placeholder-ids (internal-definition-context-placeholder-ids intdef))
    (for ([placeholder-id (in-list placeholder-ids)])
      (syntax-local-bind-syntaxes (list (syntax-local-introduce placeholder-id))
                                  #`'#,(shadowable-placeholder-transformer intdef placeholder-id)
                                  (internal-definition-context-intdef intdef)))

    (define val-bindings (reverse (internal-definition-context-val-bindings intdef)))
    (define introduced-val-bindings (for/list ([val-binding (in-list val-bindings)])
                                      (cons (map syntax-local-introduce (car val-binding))
                                            (syntax-local-introduce (cdr val-binding)))))
    (define block-expr
      (with-syntax ([([val-ids . val-expr] ...) introduced-val-bindings]
                    [(body-expr ...) (map syntax-local-introduce (reverse body-exprs))])
        #'(letrec-syntaxes+values () ([val-ids val-expr] ...) body-expr ...)))
    (define wrapped-expr (wrap-body (intdef-syntax-arm block-expr)))

    (define-values [ignored opaque-stx]
      (syntax-local-expand-expression wrapped-expr #t
                                      #:intdefs (list (internal-definition-context-intdef intdef))))

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
