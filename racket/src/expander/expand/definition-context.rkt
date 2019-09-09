#lang racket/base
(require (for-syntax racket/base)
         "../common/struct-star.rkt"
         "../common/contract.rkt"
         "../syntax/syntax.rkt"
         "../common/phase.rkt"
         "../syntax/scope.rkt"
         "../syntax/binding.rkt"
         "env.rkt"
         "use-site.rkt"
         "context.rkt"
         "main.rkt"
         "log.rkt"
         "free-id-set.rkt"
         "stop-ids.rkt"
         "reference-record.rkt"
         "body.rkt")

(provide add-intdef-scopes
         add-intdef-bindings
         internal-definition-context-frame-id
         
         internal-definition-context?
         syntax-local-make-definition-context
         syntax-local-bind-syntaxes
         internal-definition-context-binding-identifiers
         internal-definition-context-introduce
         internal-definition-context-seal
         identifier-remove-from-definition-context
         
         make-local-expand-context
         flip-introduction-scopes
         flip-introduction-and-use-scopes

         check+normalize-intdefs)

(struct internal-definition-context (frame-id      ; identifies the frame for use-site scopes
                                     scope         ; scope that represents the context
                                     add-scope?    ; whether the scope is auto-added for expansion
                                     env-mixins    ; bindings for this context: box of list of mix-binding
                                     parent-ctx))  ; parent definition context or #f

(struct env-mixin (id
                   sym
                   value
                   cache)) ; caches addition of binding to an existing environment

;; syntax-local-make-definition-context
(define/who (syntax-local-make-definition-context [parent-ctx #f] [add-scope? #t])
  (check who internal-definition-context? #:or-false parent-ctx)
  (define ctx (get-current-expand-context 'syntax-local-make-definition-context))
  (define frame-id (or (root-expand-context-frame-id ctx)
                       (and parent-ctx (internal-definition-context-frame-id parent-ctx))
                       (gensym)))
  (define sc (new-scope 'intdef))
  (define def-ctx-scopes (expand-context-def-ctx-scopes ctx))
  (when def-ctx-scopes
    (set-box! def-ctx-scopes (cons sc (unbox def-ctx-scopes))))
  (internal-definition-context frame-id sc add-scope? (box null) parent-ctx))

;; syntax-local-bind-syntaxes
(define/who (syntax-local-bind-syntaxes ids s intdef [extra-intdefs '()])
  (check who #:test (and (list? ids) (andmap identifier? ids)) #:contract "(listof identifier?)" ids)
  (check who syntax? #:or-false s)
  (check who internal-definition-context? intdef)
  (define extra-intdefs-lst (check+normalize-intdefs who extra-intdefs #:allow-single? #t))
  (define ctx (get-current-expand-context 'local-expand))
  (intdef-bind-syntaxes ctx ids s intdef extra-intdefs-lst)
  (void))

(define (intdef-bind-syntaxes ctx ids s intdef [extra-intdefs '()])
  (log-expand ctx 'local-bind ids)
  (define phase (expand-context-phase ctx))
  (define all-intdefs (cons intdef extra-intdefs))
  (define intdef-ids (for/list ([id (in-list ids)])
                       (define pre-id (remove-use-site-scopes (flip-introduction-scopes id ctx)
                                                              ctx))
                       (add-intdef-scopes (add-intdef-scopes pre-id (list intdef) #:always? #t)
                                          extra-intdefs)))
  (log-expand ctx 'rename-list intdef-ids)
  (define counter (root-expand-context-counter ctx))
  (define local-sym (and (expand-context-normalize-locals? ctx) 'loc))
  (define syms (for/list ([intdef-id (in-list intdef-ids)])
                 (add-local-binding! intdef-id phase counter
                                     #:frame-id (internal-definition-context-frame-id intdef)
                                     #:local-sym local-sym)))
  (define local-ctx
    (and s
         (let ()
           (define tmp-env (for/fold ([env (expand-context-env ctx)])
                                     ([sym (in-list syms)]
                                      [intdef-id (in-list intdef-ids)])
                             (env-extend env sym (local-variable intdef-id))))
           (make-rhs-expand-context (struct*-copy expand-context ctx
                                                  [env tmp-env])
                                    #:intdefs all-intdefs))))
  (define vals
    (cond
     [s
      (define input-s (flip-introduction-scopes (add-intdef-scopes s all-intdefs) ctx))
      (log-expand ctx 'enter-bind)
      (define vals (eval-for-syntaxes-binding 'syntax-local-bind-syntaxes input-s intdef-ids local-ctx))
      (log-expand ctx 'exit-bind)
      vals]
     [else
      (for/list ([intdef-id (in-list intdef-ids)]) (local-variable intdef-id))]))
  (define env-mixins (internal-definition-context-env-mixins intdef))
  (set-box! env-mixins (append (for/list ([intdef-id (in-list intdef-ids)]
                                          [sym (in-list syms)]
                                          [val (in-list vals)])
                                 (when local-ctx
                                   (maybe-install-free=id-in-context! val intdef-id phase local-ctx))
                                 (env-mixin intdef-id sym val (make-weak-hasheq)))
                               (unbox env-mixins)))
  (log-expand ctx 'exit-local-bind)
  (values intdef-ids syms))

;; internal-definition-context-binding-identifiers
(define/who (internal-definition-context-binding-identifiers intdef)
  (check who internal-definition-context? intdef)
  (for/list ([env-mixin (in-list (unbox (internal-definition-context-env-mixins intdef)))])
    (env-mixin-id env-mixin)))

;; internal-definition-context-introduce
(define/who (internal-definition-context-introduce intdef s [mode 'flip])
  (check who internal-definition-context? intdef)
  (check who syntax? s)
  (add-intdef-scopes s (list intdef)
                     #:always? #t
                     #:action (case mode
                                [(add) add-scope]
                                [(remove) remove-scope]
                                [(flip) flip-scope]
                                [else (raise-argument-error
                                       'internal-definition-context-introduce
                                       "(or/c 'add 'remove 'flip)"
                                       mode)])))

;; internal-definition-context-seal
(define/who (internal-definition-context-seal intdef)
  (check who internal-definition-context? intdef)
  (void))

;; identifier-remove-from-definition-context
(define/who (identifier-remove-from-definition-context id intdefs)
  (check who identifier? id)
  (define intdefs-lst (check+normalize-intdefs who intdefs #:allow-single? #t))
  (for/fold ([id id]) ([intdef (in-list intdefs-lst)])
    (internal-definition-context-introduce intdef id 'remove)))

;; For contract errors:
(define intdef?-str "internal-definition-context?")

;; Normalizes an intdefs argument that could be false or a single intdef to a list.
(define (check+normalize-intdefs who intdefs
                                 #:allow-false? [allow-false? #f]
                                 #:allow-single? [allow-single? #f])
  (define (fail)
    (define intdefs?-str (string-append "(listof " intdef?-str ")"))
    (define contract-str
      (cond
        [(and (not allow-false?) (not allow-single?))
         intdefs?-str]
        [allow-single?
         (string-append "(or/c " intdef?-str "\n"
                        "      " intdefs?-str
                        (if allow-false? "\n      #f)" ")"))]
        [allow-false?
         (string-append "(or/c " intdefs?-str " #f)")]
        [else
         intdefs?-str]))
    (raise-argument-error who contract-str intdefs))
  (cond
    [(not intdefs)
     (if allow-false? '() (fail))]
    [(list? intdefs)
     (if (andmap internal-definition-context? intdefs) intdefs (fail))]
    [else
     (if (and allow-single? (internal-definition-context? intdefs)) (list intdefs) (fail))]))

(define (add-intdef-bindings env intdefs #:only-stxs? [only-stxs? #f])
  (for/fold ([env env]) ([intdef (in-list intdefs)])
    (define parent-ctx (internal-definition-context-parent-ctx intdef))
    (define parent-env (if parent-ctx
                           (add-intdef-bindings env (list parent-ctx) #:only-stxs? only-stxs?)
                           env))
    (define env-mixins (unbox (internal-definition-context-env-mixins intdef)))
    (let loop ([env parent-env] [env-mixins env-mixins])
      (cond
       [(null? env-mixins) env]
       [else
        (define env-mixin (car env-mixins))
        (if (and only-stxs? (variable? (env-mixin-value env-mixin)))
            (loop env (cdr env-mixins))
            (or (hash-ref (env-mixin-cache env-mixin) env #f)
                (let ([new-env (env-extend (loop env (cdr env-mixins))
                                           (env-mixin-sym env-mixin)
                                           (env-mixin-value env-mixin))])
                  (hash-set! (env-mixin-cache env-mixin) env new-env)
                  new-env)))]))))

(define (add-intdef-scopes s intdefs
                           #:always? [always? #f]
                           #:action [action add-scope])
  (for/fold ([s s]) ([intdef (in-list intdefs)]
                     #:when (or always?
                        (internal-definition-context-add-scope? intdef)))
    (action s (internal-definition-context-scope intdef))))

;; ----------------------------------------

(define (make-local-expand-context ctx
                                   #:context context
                                   #:phase [phase (expand-context-phase ctx)]
                                   #:intdefs intdefs
                                   #:only-stx-intdefs? [only-stx-intdefs? #f]
                                   #:stop-ids [stop-ids #f]
                                   #:to-parsed-ok? [to-parsed-ok? #f]
                                   #:track-to-be-defined? [track-to-be-defined? #f]
                                   #:keep-#%expression? [keep-#%expression? #t])
  (define same-kind? (or (eq? context
                              (expand-context-context ctx))
                         (and (list? context)
                              (list? (expand-context-context ctx)))))
  (define all-stop-ids (and stop-ids (stop-ids->all-stop-ids stop-ids phase)))
  (define def-ctx-scopes (if (expand-context-def-ctx-scopes ctx)
                             (unbox (expand-context-def-ctx-scopes ctx))
                             null))
  (struct*-copy expand-context ctx
                [context context]
                [env (add-intdef-bindings (expand-context-env ctx)
                                          intdefs
                                          #:only-stxs? only-stx-intdefs?)]
                [use-site-scopes
                 #:parent root-expand-context
                 (and (or (eq? context 'module)
                          (eq? context 'module-begin)
                          (list? context))
                      (or (root-expand-context-use-site-scopes ctx)
                          (box null)))]
                [frame-id #:parent root-expand-context
                          ;; If there are multiple definition contexts in `intdefs`
                          ;; and if they have different frame IDs, then we conservatively
                          ;; turn on use-site scopes for all frame IDs
                          (for/fold ([frame-id (root-expand-context-frame-id ctx)]) ([intdef (in-list intdefs)])
                            (define i-frame-id (internal-definition-context-frame-id intdef))
                            (cond
                             [(and frame-id i-frame-id (not (eq? frame-id i-frame-id)))
                              ;; Special ID 'all means "use-site scopes for all expansions"
                              'all]
                             [else (or frame-id i-frame-id)]))]
                [post-expansion #:parent root-expand-context
                                (let ([pe (and same-kind?
                                               (or (pair? context)
                                                   (memq context '(module module-begin top-level)))
                                               (root-expand-context-post-expansion ctx))])
                                  (cond
                                    [(and intdefs (not (null? intdefs)))
                                     (lambda (s)
                                       (add-intdef-scopes (apply-post-expansion pe s) intdefs))]
                                    [else pe]))]
                [scopes
                 (append def-ctx-scopes
                         (expand-context-scopes ctx))]
                [only-immediate? (not stop-ids)] ; def-ctx-scopes is set for the enclosing transformer call
                [to-parsed? (if to-parsed-ok?
                                (expand-context-to-parsed? ctx)
                                #f)]
                [just-once? #f]
                [in-local-expand? #t]
                [keep-#%expression? keep-#%expression?]
                [stops (free-id-set phase (or all-stop-ids null))]
                [current-introduction-scopes null]
                [need-eventually-defined (let ([ht (expand-context-need-eventually-defined ctx)])
                                           (cond
                                             [track-to-be-defined?
                                              ;; maintain status quo and propagate tracking
                                              ht]
                                             [ht
                                              ;; keep allowing unbound references, but don't track them
                                              (make-hasheqv)]
                                             [else
                                              ;; keep disallowing unbound references
                                              #f]))]))

(define (make-rhs-expand-context ctx
                                 #:intdefs intdefs
                                 #:frame-id [frame-id #f])
  (define intdef-idss (and frame-id (map internal-definition-context-binding-identifiers intdefs)))
  (define def-ctx-scopes (expand-context-def-ctx-scopes ctx))
  (define use-site-scopes (root-expand-context-use-site-scopes ctx))
  (struct*-copy expand-context (as-expression-context ctx)
                [env (add-intdef-bindings (expand-context-env ctx) intdefs)]
                [def-ctx-scopes #f]
                [use-site-scopes #:parent root-expand-context #f]
                [scopes (append (if def-ctx-scopes (unbox def-ctx-scopes) '())
                                (if use-site-scopes (unbox use-site-scopes) '())
                                (expand-context-scopes ctx))]
                [reference-records (if frame-id
                                       (cons frame-id (expand-context-reference-records ctx))
                                       (expand-context-reference-records ctx))]
                [binding-layer (if frame-id
                                   (increment-binding-layer intdef-idss ctx frame-id)
                                   (expand-context-binding-layer ctx))]
                [only-immediate? #f]
                [just-once? #f]
                [in-local-expand? #t]
                [keep-#%expression? #f]
                [stops empty-free-id-set]
                [current-introduction-scopes '()]))

;; ----------------------------------------

(define (flip-introduction-scopes s ctx)
  (flip-scopes s (expand-context-current-introduction-scopes ctx)))

(define (flip-introduction-and-use-scopes s ctx)
  (flip-scopes (flip-introduction-scopes s ctx)
               (expand-context-current-use-scopes ctx)))
