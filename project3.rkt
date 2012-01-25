#lang plai

(print-only-errors #true)

; represents a function definition
(define-type FunDef
  (fundef (name symbol?) (params (listof symbol?)) (body CF1WAE?)))
 
; represents a binding in a with expression
(define-type Binding
  [binding (name symbol?) (named-expr CF1WAE?)])

; represents an expression
(define-type CF1WAE
  [num (n number?)]
  ;[str (s string?)]
  ;[bool (b boolean?)]
  ;[mt]
  ;[unop (op any/c) (arg CF1WAE?)]
  [binop (op any/c) (lhs CF1WAE?) (rhs CF1WAE?)]
  [with (lob (listof Binding?)) (body CF1WAE?)]
  [varref (name symbol?)]
  ;[switch (val CF1WAE?) (clauses (listof SClause?)) (elseval CF1WAE?)]
  [app (f symbol?) (arg CF1WAE?)])

;; parse : s-exp -> CF1WAE
;; Consumes an s-expression and generates the corresponding CF1WAE
(define (parse sexp)
  (match sexp
    [(? number? n)                   (num n)]
    [(? symbol? s)                   (varref s)]
    [(list (? op-symbol? s) lhs rhs) (binop (symbol->op s) (parse lhs) (parse rhs))]
    [(list 'with (? list? bindings) body)
                                     (with (map parse-binding bindings) 
                                           (parse body))]
    [(list (? symbol? name) arg) (app name (parse arg))]
    [else                            (error 'parse "* bad syntax: ~v" sexp)]))

;; parse-binding : sexp -> Binding
;; Consumes an s-expression and generates a Binding
(define (parse-binding b)
 (match b
   [(list (? symbol? name) '= rhs) (binding name (parse rhs))]
   [else (error 'parse-binding "bad syntax for binding: ~v" b)]))

;; op-symbol? : symbol -> boolean
;; returns true exactly when s is a symbol representing a legal binop
(define (op-symbol? s)
  (member s (list '+ '- '* '/)))

;; symbol->op : symbol -> (number number -> number)
;; Returns the binop that corresponds to a binop symbol
(define (symbol->op s)
  (case s [(+) +] [(-) -] [(*) *] [(/) /] 
    [else (error 'symbol->op 
                 "internal error: expected binop-symbol, got: ~v" s)]))

;(test/exn (symbol->op 'ab) "internal error")

;; test cases for the parser

(let ([n11 (num 11)]
      [n12 (num 12)])
 
  (test (parse '13) (num 13))
  (test (parse '{+ 11 12}) (binop + n11 n12))
  (test (parse '{- 11 12}) (binop - n11 n12))
  (test (parse '{* 11 12}) (binop * n11 n12))
  (test (parse '{/ 11 12}) (binop / n11 n12))
  (test (parse '{* {+ 11 12} 11}) (binop * (binop + n11 n12) n11))
  (test (parse '{with {{ab = {+ 11 12}} {cd = {with {{de = 4}} 6}}} cd})
        (with (list (binding 'ab (binop + n11 n12))
                    (binding 'cd (with (list (binding 'de (num 4))) (num 6))))
              (varref 'cd)))
  (test (parse '{with {} {+ 3 4}})
        (with (list) (binop + (num 3) (num 4))))
  (test (parse '{with {{z = 4} {y = 9}} {+ y z}})
        (with (list (binding 'z (num 4))
                    (binding 'y (num 9)))
              (binop + (varref 'y) (varref 'z))))
  ;; error checking
  (test/exn (parse '{+ 3 4 5}) "bad syntax")
  (test/exn (parse '{_ 2 3}) "bad syntax")
  (test/exn (parse '{with {} 3 4 5}) "bad syntax")
  (test/exn (parse "abc") "bad syntax")
  (test/exn (parse '{with 3 4}) "bad syntax")
  (test/exn (parse '{with {{a b c}} 4}) "bad syntax")
  (test/exn (parse '{with {{3 4}} 4})  "bad syntax"))

(test (parse '{func (+ 1 2)}) (app 'func (binop + (num 1) (num 2))))
(test (parse '{func 1}) (app 'func (num 1)))
(test (parse '{double {double 5}}) (app 'double (app 'double (num 5))))
(test (parse '{+ {f 5} {g 6}}) (binop + (app 'f (num 5)) (app 'g (num 6))))

; interp : CF1WAE? immutable-hash-table? (listof FunDef?) -> CF1WAE-Value?
; This procedure interprets the given CF1WAE in the given
;  environment with the given function definitions and
;  produces a result in the form of a CF1WAE-Value
(define (interp exp env defs)
  (type-case CF1WAE exp
    [num (n) n]
    [binop (op l r) (op (interp l) (interp r))]
    [with (bindings body)
          (begin
            (define names (map binding-name bindings))
            (define rhses (map binding-named-expr bindings))
            (when (overlapping? names)
              (error 'interp 
                     "var name appears more than once in bindings: ~v"
                     names))
            (define rhs-vals (map num (map interp rhses env defs)))
            (define new-env (map hash-set env names rhs-vals))
            (interp body new-env defs))]
    [app (name args) 
         (type-case FunDef (lookup-fundef name defs)
           [fundef (name param body)
                   (let ()
                     (define argval (interp args env defs))
                     (define new-env (hash param argval))           
                     (interp body new-env defs))])]
    [varref (s) (lookup-env s env)]))

; lookup-fundef : symbol fundef -> fundef
(define (lookup-fundef fun-name fundefs)
  (cond
    [(empty? fundefs) (error fun-name "function not found")]
    [else (if (symbol=? fun-name (fundef-name (first fundefs)))
              (first fundefs)
              (lookup-fundef fun-name (rest fundefs)))]))

; lookup-env : symbol env -> CF1WAE
(define (lookup-env name env)
  (cond
    [(hash-has-key? env name) (hash-ref env name)]
    [else (error "variable not defined")]))

;; overlapping : (listof symbol?) -> boolean?
;; returns true when a symbol appears more than once in the list
(define (overlapping? syms)
  (cond [(empty? syms) false]
        [else (or (member (first syms) (rest syms))
                  (overlapping? (rest syms)))]))

;; test cases for overlapping?
(test (overlapping? '(a b c b d)) '(b d))
(test (overlapping? '(a b c d e)) false)

;; interp tests
(define unbound-var-msg "unbound variable")
(define duplicated-var-msg "var name appears more than once")

(test (interp (parse '3) (hash) empty) 3)
;(test (interp (parse '{+ 3 4})) 7)
;(test (interp (parse '{/ 12 6})) 2)
;(test (interp (parse '{* 12 7})) 84)
;(test (interp (parse '{- 12 5})) 7)
(interp (parse '{with {{a = 6}} 5}) (hash) empty)
(test (interp (parse '{with {{a = 6}} 5}) (hash) empty) 5)
;(test (interp (parse '{with {{a = 6}} a})) 6)
;(test (interp (parse '{with {{a = 6}} {+ a 13}})) 19)
;(test (interp (parse '{with {{a = 7} {b = 8}} {+ 4 {* a b}}})) 60)
;(test/exn (interp (parse '{with {{a = 7} {b = 3} {a = 9}} 13})) duplicated-var-msg)
;(test/exn (interp (parse '{with {{a = 7}} b})) unbound-var-msg)