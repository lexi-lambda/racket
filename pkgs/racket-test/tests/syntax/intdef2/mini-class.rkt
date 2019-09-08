#lang racket/base

(require racket/require
         (for-syntax (subtract-in racket/base syntax/intdef2)
                     racket/list
                     racket/set
                     syntax/transformer)
         racket/format
         racket/set
         racket/stxparam
         racket/unsafe/undefined
         syntax/parse/define
         syntax/intdef2)

(module+ test
  (require rackunit))

;; local
(define-syntax local
  (make-expression-transformer
   (syntax-parser
     [(_ [local-defn-or-expr ...] defn-or-expr ...+)
      #:do [(define intdef (syntax-local-make-internal-definition-context))
            (for ([local-defn-or-expr (in-list (attribute local-defn-or-expr))])
              (syntax-local-internal-definition-context-extend! intdef local-defn-or-expr))
            (syntax-local-internal-definition-context-extend! intdef #'(let () defn-or-expr ...))]
      (syntax-local-internal-definition-context-finish! intdef)])))

(module+ test
  (check-equal? (local [(define x 2)
                        (define y (* x 3))]
                  (define x (+ y 4))
                  (/ x 2))
                5))

;; mini-class
(define-for-syntax (mini-class-keyword stx)
  (raise-syntax-error #f "cannot be used as an expression" stx))
(define-syntaxes [init field define/public]
  (values mini-class-keyword mini-class-keyword mini-class-keyword))
(define-for-syntax mini-class-keywords (list #'init #'field #'define/public))

(define-syntax (this-out-of-context stx)
  (raise-syntax-error #f "cannot be used outside class body" stx))
(define-rename-transformer-parameter this-param (make-rename-transformer #'this-out-of-context))
(define-syntax this (make-variable-like-transformer #'this-param))

(define-syntax (init-out-of-context stx)
  (raise-syntax-error #f "init arg out of context" stx))
(define-syntax (init-in-method stx)
  (raise-syntax-error #f "cannot reference init arg inside method body" stx))

(struct class (methods field-names initializer))
(struct object (class fields))

(define new
  (make-keyword-procedure
   (lambda (kws kw-args cls)
     (define obj (object cls (make-hasheq (for/list ([kw (in-set (class-field-names cls))])
                                            (cons kw unsafe-undefined)))))
     (keyword-apply (class-initializer cls) kws kw-args (list obj))
     obj)))

(define (check-field-not-unsafe-undefined name v #:assign? [assign? #f])
  (if (eq? v unsafe-undefined)
      (raise (exn:fail:contract:variable (~a name ": undefined; "
                                             (if assign? "assignment" "use")
                                             " before initialization")
                                         (current-continuation-marks)
                                         (string->symbol (keyword->string name))))
      v))

(define (dynamic-get-field this name)
  (check-field-not-unsafe-undefined name (hash-ref (object-fields this) name)))
(define (dynamic-set-field!/no-check this name value)
  (hash-set! (object-fields this) name value))
(define (dynamic-set-field! this name value)
  (check-field-not-unsafe-undefined name (hash-ref (object-fields this) name) #:assign? #t)
  (dynamic-set-field!/no-check this name value))
(define dynamic-send
  (make-keyword-procedure
   (lambda (kws kw-args this name . args)
     (keyword-apply (hash-ref (class-methods (object-class this)) name) kws kw-args this args))))

(define-syntax-parser get-field
  [(_ e:expr kw:keyword)
   (syntax/loc this-syntax
     (dynamic-get-field e 'kw))])
(define-syntax-parser set-field!
  [(_ e:expr kw:keyword val-e:expr)
   (syntax/loc this-syntax
     (dynamic-set-field! e 'kw val-e))])
(define-syntax-parser send
  [(_ e:expr kw:keyword . formals)
   (syntax/loc this-syntax
     (dynamic-send e 'kw . formals))])

(define-syntax mini-class
  (make-expression-transformer
   (syntax-parser
     [(_ class-decl ...)
      #:do [(define intdef (syntax-local-make-internal-definition-context))

            (define inits (make-hasheq))
            (define fields (mutable-seteq))
            (define methods (make-hasheq))

            (define interpret
              (syntax-parser
                #:literals [init field define/public]

                [(init ~! {~seq kw:keyword x:id} ...+)
                 #:fail-when (or (check-duplicates (attribute kw) eq? #:key syntax-e)
                                 (for/or ([kw (in-list (attribute kw))])
                                   (and (hash-has-key? inits (syntax-e kw))
                                        kw)))
                 "duplicate init arg name"
                 #:with [x-param ...] (syntax-local-internal-definition-context-bind-placeholders!
                                       intdef
                                       (generate-temporaries (attribute x)))
                 (for ([kw (in-list (attribute kw))]
                       [x-param (in-list (attribute x-param))])
                   (hash-set! inits (syntax-e kw) (syntax-local-introduce x-param)))
                 #'(begin
                     (define-syntax x (make-variable-like-transformer
                                       (quote-syntax (#%expression x-param))))
                     ...)]

                [(field ~! {~seq kw:keyword e:expr} ...)
                 #:fail-when (or (check-duplicates (attribute kw) eq? #:key syntax-e)
                                 (for/or ([kw (in-list (attribute kw))])
                                   (and (set-member? fields (syntax-e kw))
                                        kw)))
                 "duplicate field name"
                 (for ([kw (in-list (attribute kw))])
                   (set-add! fields (syntax-e kw)))
                 #'(begin (dynamic-set-field!/no-check this 'kw e) ...)]

                [(define/public ~! (kw:keyword . formals) body-defn-or-expr ...+)
                 #:fail-when (and (hash-has-key? methods (syntax-e #'kw)) #'kw)
                 "duplicate method name"
                 (hash-set! methods
                            (syntax-e #'kw)
                            (syntax-local-introduce
                             (syntax/loc this-syntax
                               (lambda (this-val . formals)
                                 (syntax-parameterize ([this-param (make-rename-transformer
                                                                    #'this-val)])
                                   body-defn-or-expr ...)))))
                 #'(begin)]

                [_
                 #f]))

            (for ([class-decl (in-list (attribute class-decl))])
              (syntax-local-internal-definition-context-extend! intdef class-decl
                                                                #:stop-ids mini-class-keywords
                                                                #:compile interpret))
            (syntax-local-internal-definition-context-extend! intdef #'(void))]

      #:with [(init-kw . init-id) ...] (for/list ([(kw id) (in-hash inits)])
                                         (cons kw (syntax-local-introduce id)))
      #:with [init-tmp ...] (generate-temporaries (attribute init-id))
      #:with [field-kw ...] (set->list fields)
      #:with [(method-kw . method-e) ...] (for/list ([(kw e) (in-hash methods)])
                                            (cons kw (syntax-local-introduce e)))
      (syntax-local-internal-definition-context-finish!
       intdef
       #:wrap
       (lambda (body-stx)
         #`(let ()
             (define-rename-transformer-parameter init-id
               (make-rename-transformer #'init-out-of-context))
             ...
             (class (syntax-parameterize ([init-id (make-rename-transformer #'init-in-method)] ...)
                      (hasheq {~@ 'method-kw method-e} ...))
               (seteq 'field-kw ...)
               (lambda (this-val {~@ init-kw init-tmp} ...)
                 (syntax-parameterize ([this-param (make-rename-transformer #'this-val)]
                                       [init-id (make-rename-transformer (quote-syntax init-tmp))]
                                       ...)
                   #,body-stx))))))])))

(module+ test
  (define-simple-macro (attr-accessor kw:keyword e:expr)
    #:do [(define kw-str (keyword->string (syntax-e #'kw)))]
    #:with get-kw (datum->syntax #f (string->keyword (string-append "get-" kw-str)) #'kw)
    #:with set!-kw (datum->syntax #f (string->keyword (string-append "set-" kw-str "!")) #'kw)
    (begin
      (field kw e)
      (define/public (get-kw)
        (get-field this kw))
      (define/public (set!-kw val)
        (set-field! this kw val))))

  (define box%
    (mini-class
     (init #:value value)
     (attr-accessor #:value value)
     #;(define/public (#:bad)
         value)))

  (define b (new box% #:value #f))
  (check-equal? (send b #:get-value) #f)
  (send b #:set-value! #t)
  (check-equal? (send b #:get-value) #t))
