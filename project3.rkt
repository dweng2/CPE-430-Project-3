#lang plai

(print-only-errors #true)

; represents a function definition
(define-type FunDef
  (fundef (name symbol?) (params (listof symbol?)) (body CF1WAE?)))
 
; represents a binding in a with expression
(define-type Binding
  [binding (name symbol?) (named-expr CF1WAE?)])

; represents a 'switch' clause
(define-type SClause
  [clause (patval CF1WAE?) (result CF1WAE?)])

; represents an expression
(define-type CF1WAE
  [num (n number?)]
  [str (s string?)]
  [bool (b boolean?)]
  [mt]
  [unop (op any/c) (arg CF1WAE?)]
  [binop (op any/c) (lhs CF1WAE?) (rhs CF1WAE?)]
  [with (lob (listof Binding?)) (body CF1WAE?)]
  [varref (name symbol?)]
  [switch (val CF1WAE?) (clauses (listof SClause?)) (elseval CF1WAE?)]
  [app (f symbol?) (args (listof CF1WAE?))])

; represents a possible result of evaluation
(define-type CF1WAE-Value
  [numV (n number?)]
  [strV (s string?)]
  [boolV (b boolean?)]
  [mtV]
  [pairV (first CF1WAE-Value?) (rest CF1WAE-Value?)])

; error message for a type error
(define type-error "Type Error")

; parse-fun : s-exp? -> FunDef?
; This procedure parses an s-expression into a FunDef
(define (parse-fun exp)
  (match exp
    [(list 'fun (? symbol? name) (? list? params) body)
     (begin
       (valid-name name)
       (for-each valid-name params)
       (when (overlapping? params)
         (error 'parse-fun 
                "param name appears more than once in function def ~v"
                params))
       (fundef name params (parse-exp body)))]
    [else (error "Bad function def syntax")]))

(define (valid-name name) 
  (when (or (unop-symbol? name) (binop-symbol? name) (symbol=? 'with name))
         (error "Invalid function name")))

;; overlapping : (listof symbol?) -> boolean?
;; returns true when a symbol appears more than once in the list
(define (overlapping? syms)
  (cond [(empty? syms) false]
        [else (or (member (first syms) (rest syms))
                  (overlapping? (rest syms)))]))

;; parse-exp : s-exp -> CF1WAE
;; Consumes an s-expression and generates the corresponding CF1WAE
(define (parse-exp sexp)
  (match sexp
    [(? number? n)           (num n)]
    [(? string? s)           (str s)]
    ['true (bool #t)]
    ['false (bool #f)]
    ['null (mt)] 
    [(? symbol? s)
     (begin
       (valid-name s)
       (varref s))]
    [(list (? unop-symbol? s) body) (unop s (parse-exp body))]
    [(list (? binop-symbol? s) lhs rhs) (binop s (parse-exp lhs) (parse-exp rhs))]
    [(list 'with (? list? bindings) body)
     (begin
       (define names (map first bindings))
       (when (overlapping? names)
         (error 'parse-exp 
                "var name appears more than once in bindings: ~v"
                names))
       (with (map parse-binding bindings) 
             (parse-exp body)))]
    [(list 'switch val c ... (list 'else l)) 
     (switch (parse-exp val) (map parse-clause c) (parse-exp l))]
    [(list (? symbol? name) args ...)
     (begin
       (valid-name name)
       (app name (map parse-exp args)))]
    [else (error 'parse-exp "* bad syntax: ~v" sexp)]))

; listof list -> listof SClauses
(define (parse-clause in)
  (match in
    [(list val '=> b) (clause (parse-exp val) (parse-exp b))]
    [else (error "bad syntax in switch statement")]))

;; parse-binding : sexp -> Binding
;; Consumes an s-expression and generates a Binding
(define (parse-binding b)
 (match b
   [(list (? symbol? name) '= rhs) (binding name (parse-exp rhs))]
   [else (error 'parse-binding "bad syntax for binding: ~v" b)]))

;; op-symbol? : symbol -> boolean
;; returns true exactly when s is a symbol representing a legal binop
(define (binop-symbol? s)
  (member s (list '+ '- '* '/ 'equal? '<= 'pair 'and 'or)))

;; op-symbol? : symbol -> boolean
;; returns true exactly when s is a symbol representing a legal binop
(define (unop-symbol? s)
  (member s (list 'not 'number? 'pair? 'string? 'null? 'first 'rest)))

;; symbol->op : symbol -> (number number -> number)
;; Returns the op that corresponds to a op symbol
(define (symbol->op s)
  (case s 
    [(+) (lambda (a b)(check_type_2 + number? (get-value a) (get-value b)))]
    [(-) (lambda (a b)(check_type_2 - number? (get-value a) (get-value b)))]
    [(*) (lambda (a b)(check_type_2 * number? (get-value a) (get-value b)))] 
    [(/) (lambda (a b)(check_type_2 / number? (get-value a) (get-value b)))]
    [(not) (lambda (a)(check_type_1 not boolean? (get-value a)))]
    [(and) (lambda (a b)(check_type_2 (lambda (x y) (and x y)) boolean? (get-value a) (get-value b)))]
    [(or) (lambda (a b)(check_type_2 (lambda (x y) (or x y)) boolean? (get-value a) (get-value b)))]    
    [(equal?) equal?]
    [(<=) (lambda (a b)(check_type_2 <= number? (get-value a) (get-value b)))]
    [(number?) numV?]
    [(pair?) pairV?]
    [(pair) (lambda (a b) (pairV a b))]
    [(string?) strV?]
    [(null?) mtV?]
    [(first) (lambda (a)(check_type_1 pairV-first pairV? a))]
    [(rest) (lambda (a)(check_type_1 pairV-rest pairV? a))]
    [else (error 'symbol->op 
                 "internal error: expected binop-symbol, got: ~v" s)]))

(test/exn (symbol->op 'asdf) "internal")

; type checking functions
(define (check_type_2 func type a b)
  (unless (type a) (error type-error))
  (unless (type b) (error type-error))
  (func a b))

(define (check_type_1 func type a)
  (unless (type a) (error type-error))
  (func a))

;(test/exn (symbol->op 'ab) "internal error")

;; test cases for the parser

(let ([n11 (num 11)]
      [n12 (num 12)])
 
  (test (parse-exp '13) (num 13))
  (test (parse-exp '{+ 11 12}) (binop '+ n11 n12))
  (test (parse-exp '{- 11 12}) (binop '- n11 n12))
  (test (parse-exp '{* 11 12}) (binop '* n11 n12))
  (test (parse-exp '{/ 11 12}) (binop '/ n11 n12))
  (test (parse-exp '{* {+ 11 12} 11}) (binop '* (binop '+ n11 n12) n11))
  (test (parse-exp '{with {{ab = {+ 11 12}} {cd = {with {{de = 4}} 6}}} cd})
        (with (list (binding 'ab (binop '+ n11 n12))
                    (binding 'cd (with (list (binding 'de (num 4))) (num 6))))
              (varref 'cd)))
  (test (parse-exp '{with {} {+ 3 4}})
        (with (list) (binop '+ (num 3) (num 4))))
  (test (parse-exp '{with {{z = 4} {y = 9}} {+ y z}})
        (with (list (binding 'z (num 4))
                    (binding 'y (num 9)))
              (binop '+ (varref 'y) (varref 'z))))
  ;; error checking
  (test/exn (parse-exp '{+ 3 4 5}) "Invalid function")
  (test (parse-exp '{_ 2 3}) (app '_ (list (num 2) (num 3))))
  (test/exn (parse-exp '{with {} 3 4 5}) "Invalid function")
  (test/exn (parse-exp '{with 3 4}) "Invalid function")
  (test/exn (parse-exp '{with {{a b c}} 4}) "bad syntax")
  (test/exn (parse-exp '{with {{3 4}} 4})  "bad syntax"))

(test (parse-exp '{func (+ 1 2)}) (app 'func (list (binop '+ (num 1) (num 2)))))
(test (parse-exp '{func 1}) (app 'func (list (num 1))))
(test (parse-exp '{double {double 5}}) (app 'double (list (app 'double (list (num 5))))))
(test (parse-exp '{+ {f 5} {g 6}}) (binop '+ (app 'f (list (num 5))) (app 'g (list (num 6)))))

(test (parse-exp 'true) (bool true))
(test (parse-exp 'false) (bool false))
(test (parse-exp '{not true}) (unop 'not (bool true)))

(test (parse-exp '{switch {get-fruit 2}
   ["apple" => "good choice!"]
   [else "I don't recognize your so-called 'fruit'."]})
      (switch (app 'get-fruit (list (num 2))) 
              (list (clause (str "apple") (str "good choice!")))
              (str "I don't recognize your so-called 'fruit'.")))

(test/exn (parse-exp '{switch {get-fruit 2}
   ["apple" => "good choice!"]
   [else "excellent choice!"]
   [else "I don't recognize your so-called 'fruit'."]}) "switch statement")
(test/exn (parse-exp '{switch {get-fruit 2}
   ["apple" => "good choice!"]}) "bad syntax")

(test (parse-exp '{pair null null}) (binop 'pair (mt) (mt)))
(test (parse-exp '{pair "String" null}) (binop 'pair (str "String") (mt)))

(test (parse-fun '{fun my-fun {x} (+ x x)}) (fundef 'my-fun (list 'x) (binop '+ (varref 'x) (varref 'x))))
(test (parse-fun '{fun one {} {+ 1 1}}) (fundef 'one '() (binop '+ (num 1) (num 1))))
(test/exn (parse-fun '{adf a a}) "def syntax")
(test/exn (parse-exp '{z with}) "Invalid function")
; interp : CF1WAE? immutable-hash-table? (listof FunDef?) -> CF1WAE-Value?
; This procedure interprets the given CF1WAE in the given
;  environment with the given function definitions and
;  produces a result in the form of a CF1WAE-Value
(define (interp exp env defs)
  (type-case CF1WAE exp
    [num (n) (numV n)]
    [str  (s) (strV s)]
    [bool (b) (boolV b)]
    [mt () (mtV)]
    [unop (op body) (make-value ((symbol->op op) (interp body env defs)))]
    [binop (op l r) (make-value ((symbol->op op) (interp l env defs)  
                                                 (interp r env defs)))]
    [with (bindings body)
          (begin
            (define names (map binding-name bindings))
            (define rhses (map binding-named-expr bindings))
            (define rhs-vals (map (lambda (expr) (interp expr env defs)) rhses))            
            (define new-env (foldl (lambda (n v e) (hash-set e n v)) env names rhs-vals))
            (interp body new-env defs))]
    [app (name args) 
         (type-case FunDef (lookup-fundef name defs)
           [fundef (name params body)
                   (let ()
                     (define argvals (map (lambda (expr) (interp expr env defs)) args))
                     (define new-env (foldl (lambda (n v e) (hash-set e n v)) (hash) params argvals))
                     (interp body new-env defs))])]
    [switch (val clauses elseval) 
            (begin
              (define equal-exprs (append (map clause-patval clauses) (list val)))
              (define equal-vals (map (lambda (expr) (interp expr env defs)) equal-exprs))
              (define clause-body (append (map clause-result clauses) (list elseval)))
              (interp (ormap (lambda (x y) (eval-clause (interp val env defs) x y)) 
                             equal-vals clause-body) 
                      env defs))]
    [varref (s) (lookup-env s env)]))

; lookup-fundef : symbol fundef -> fundef
(define (lookup-fundef fun-name fundefs)
  (cond
    [(empty? fundefs) (error fun-name "function not found")]
    [(symbol=? fun-name (fundef-name (first fundefs))) (first fundefs)]
    [else (lookup-fundef fun-name (rest fundefs))]))

; lookup-env : symbol env -> number
(define (lookup-env name env)
  (cond
    [(hash-has-key? env name) (hash-ref env name)]
    [else (error "variable not defined")]))

; get-value : CF1WAE-Value -> value
; pulls the values out of the CF1WAE-Value
(define (get-value in)
  (type-case CF1WAE-Value in
    [numV (n) n]
    [strV (s) s]
    [boolV (b) b]
    [else in]))

(define (make-value in)
  (cond
    [(number? in) (numV in)]
    [(boolean? in) (boolV in)]
    [(string? in) (strV in)]
    [else in]))

(test (make-value "str") (strV "str"))
(test (get-value (mtV)) (mtV))

(define (eval-clause check equal-val body)
  (cond
    [(equal? check equal-val) body]
    [else #f]))

;; test cases for overlapping?
(test (overlapping? '(a b c b d)) '(b d))
(test (overlapping? '(a b c d e)) false)

;; interp tests
(define unbound-var-msg "unbound variable")
(define duplicated-var-msg "var name appears more than once")

(test (interp (parse-exp '3) (hash) empty) (numV 3))
(test (interp (parse-exp '{+ 3 4}) (hash) empty) (numV 7))
(test (interp (parse-exp '{/ 12 6}) (hash) empty) (numV 2))
(test (interp (parse-exp '{* 12 7}) (hash) empty) (numV 84))
(test (interp (parse-exp '{- 12 5}) (hash) empty) (numV 7))
(test (interp (parse-exp '{with {{a = 6}} 5}) (hash) empty) (numV 5))
(test (interp (parse-exp '{with {{a = 6}} a}) (hash) empty) (numV 6))
(test (interp (parse-exp '{with {{a = 6}} {+ a 13}}) (hash) empty) (numV 19))
(test (interp (parse-exp '{with {{a = 7} {b = 8}} {+ 4 {* a b}}}) (hash) empty) (numV 60))
(test/exn (interp (parse-exp '{with {{a = 7}} b}) (hash) empty) "not defined")

(test (interp (parse-exp '{number? 1}) (hash) empty) (boolV #t))
(test (interp (parse-exp '{a 5}) (hash) (list (parse-fun '{fun a {x} x}))) (numV 5))
(test (interp (parse-exp '{with {{x = 1}} {a 7}}) (hash) (list (fundef 'a (list 'x) (varref 'x)))) (numV 7))
(test/exn (interp (parse-exp '{a 5}) (hash) empty) "function not")
(test (interp (parse-exp '{not true}) (hash) empty) (boolV false))
(test/exn (interp (parse-exp '{not 6}) (hash) empty) type-error)
(test/exn (interp (parse-exp '{+ true false}) (hash) empty) type-error)
(test (interp (parse-exp "aString") (hash) empty) (strV "aString"))
(test (interp (parse-exp '{equal? 1 1}) (hash) empty) (boolV true))
(test (interp (parse-exp '{equal? 1 2}) (hash) empty) (boolV false))
(test (interp (parse-exp '{equal? "bob" "bob"}) (hash) empty) (boolV true))
(test (interp (parse-exp '{<= 1 2}) (hash) empty) (boolV true))
(test (interp (parse-exp '{<= 10 2}) (hash) empty) (boolV false))
(test (interp (parse-exp '{switch true [true => true][else false]}) (hash) empty) (boolV true))
(test (interp (parse-exp '{switch false [true => true][else false]}) (hash) empty) (boolV false))
(test (interp (parse-exp '{switch true [true => (+ 10 5)][else false]}) (hash) empty) (numV 15))
(test (interp (parse-exp '{switch (+ 1 1) [2 => true][else false]}) (hash) empty) (boolV true))
(test (interp (parse-exp '{switch "durian"
   ["apple" => "good choice!"]
   ["banana" => "excellent choice!"]
   ["durian" => "Hmm, I'm not sure your taxi driver is going to like that."]
   [else "I don't recognize your so-called 'fruit'."]}) (hash) empty) (strV "Hmm, I'm not sure your taxi driver is going to like that."))

(test (interp (parse-exp '{pair null null}) (hash) empty) (pairV (mtV) (mtV)))
(test (interp (parse-exp '{pair "string" null}) (hash) empty) (pairV (strV "string") (mtV)))
(test (interp (parse-exp '{pair? {pair null null}}) (hash) empty) (boolV true))
(test (interp (parse-exp '{null? null}) (hash) empty) (boolV true))
(test (interp (parse-exp '{first {pair "string" null}}) (hash) empty) (strV "string"))
(test (interp (parse-exp '{rest {pair "string" null}}) (hash) empty) (mtV))
(test (interp (parse-exp '{rest {pair "string" {pair "bob" null}}}) (hash) empty) (pairV (strV "bob") (mtV)))
(test/exn (interp (parse-exp '{a 5}) (hash) (list (parse-fun '(fun a (x x) x)))) "param")

(test (interp (parse-exp '{and true true}) (hash) empty) (boolV true))
(test (interp (parse-exp '{or false true}) (hash) empty) (boolV true))
(test (interp (parse-exp '{string? "adfaf"}) (hash) empty) (boolV true))
(test/exn (interp (parse-exp '{and true "t"}) (hash) empty) type-error)
(test (interp (parse-exp '{b 5}) (hash) (list (parse-fun '{fun a {x} x}) (parse-fun '{fun b {x} x}))) (numV 5))
(test/exn (parse-exp '{with {{x = 3}{x = 4}}x}) "more than once")
(interp (parse-exp '{with {{a = 1}} {with {{b = 2}} {+ a b}}}) (hash) empty)
;(test (interp (parse-exp '{with {{a = 4} {b = 5} {with {{c = {* b 4}} {d = {+ 4 a}}} {+ {- b c} {* a d}}}}})))