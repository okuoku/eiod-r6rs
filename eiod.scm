;; eiod.scm: eval-in-one-define
;; Copyright 2002 Al Petrofsky <al@petrofsky.org>
;; $Id$
;;
;; A minimal implementation of r5rs eval, null-environment, and
;; scheme-report-environment.

;; Data Structures:

;; An environment is a procedure that takes an identifier and returns
;; a denotation.  A denotation is either a binding, or, for unbound
;; identifiers, it is a symbol that represents the identifier's
;; original name.  A binding is a mutable pair of an identifier and
;; its value.

;; denotation:  [symbol | binding]
;; binding:     (identifier . [value | syntax])
;; syntax:      ([builtin | transformer] . marker)
;; identifier:  [symbol | (denotation . marker)]

;; A value is any arbitrary scheme value.  Syntaxes (special forms)
;; are stored in pairs whose cdr is the eq?-unique marker object (this
;; makes them distinguishable from ordinary pair values in a variable
;; binding).  The car is either a symbol naming a builtin, or a
;; transformer procedure that takes two arguments: a macro use and the
;; environment of the macro use.

;; When a macro template containing a literal identifier is expanded,
;; the identifier is replaced with a fresh identifier, which is a new
;; pair whose cdr is the marker object (which makes such identifiers
;; distinguishable from ordinary pairs in a source-code s-expression).
;; The fresh identifier's car is the old identifier's denotation in
;; the environment of the macro's definition.  When one of these
;; "renamed" identifiers is lookep up in an environment that has no
;; binding for it, the old denotation is returned.

;; This environment and denotation model is similar to the one
;; described in the 1991 paper "Macros that Work" by Clinger and Rees.

;; The base environment contains eight syntax bindings and two
;; variable bindings:
;;   lambda, set!, and begin are as in the standard.
;;   q is like quote, but it does not handle pairs or vectors.
;;   def is like define, but it does not handle the (f . args) format.
;;   (get-env) returns the local environment.
;;   (syntax x) is like quote, but does not convert identifiers to symbols.
;;   (macro x) evaluates x to get a transformer procedure and makes a macro.
;;   The id? procedure is a predicate for identifiers.
;;   The new-id procedure takes a denotation and returns a fresh identifier.


;; Quote-and-evaluate captures all the code into the list eiod-source
;; so that we can feed eval to itself.  The matching close parenthesis
;; is at the end of the file.

(define-syntax quote-and-evaluate
  (syntax-rules () ((_ var . x) (begin (define var 'x) . x))))

(quote-and-evaluate eiod-source

(define eval
  (let ()
    (define marker      (vector '*eval-marker*))
    (define (mark x)    (cons x marker))
    (define unmark      car)
    (define (marked? x) (and (pair? x) (eq? marker (cdr x))))
    (define (id? sexp)  (or (symbol? sexp) (marked? sexp)))

    (define (make-builtins-env)
      (define syntaxes '(lambda set! q def begin syntax macro get-env))
      (let ((alist `((id? . ,id?)
		     (new-id . ,mark)
		     . ,(map cons syntaxes (map mark syntaxes)))))
	(lambda (id) (or (assq id alist) (if (symbol? id) id (unmark id))))))

    (define (env-add id val env)
      (define binding (cons id val))
      (lambda (i) (if (eq? id i) binding (env i))))

    (define (xeval sexp env)
      (let eval-in-this-env ((sexp sexp))
	(cond ((id? sexp) (cdr (env sexp)))
	      ((not (pair? sexp)) sexp)
	      (else (let ((head (eval-in-this-env (car sexp)))
			  (tail (cdr sexp)))
		      (if (marked? head)
			  (case (unmark head)
			    ((get-env) env)
			    ((syntax) (car tail))
			    ((lambda) (eval-lambda tail env))
			    ((begin) (eval-begin tail env))
			    ((macro) (mark (eval-in-this-env (car tail))))
			    ((set!) (set-cdr! (env (car tail))
					      (eval-in-this-env (cadr tail))))
			    ((q) (do ((x tail (car x)))
				     ((not (pair? x)) x)))
			    (else (eval-in-this-env ((unmark head) sexp env))))
			  (apply head (map eval-in-this-env tail))))))))

    (define (eval-begin tail env)
      ;; Don't use for-each because we must tail-call the last expression.
      (do ((sexps tail (cdr sexps)))
	  ((null? (cdr sexps)) (xeval (car sexps) env))
	(xeval (car sexps) env)))

    (define (eval-lambda tail env)
      (lambda args
	(define ienv (do ((args args (cdr args))
			  (vars (car tail) (cdr vars))
			  (ienv env (env-add (car vars) (car args) ienv)))
			 ((or (null? vars) (id? vars))
			  (if (null? vars) ienv (env-add vars args ienv)))))
	(let loop ((ienv ienv) (vars '()) (inits '()) (body (cdr tail)))
	  (define (ieval sexp) (xeval sexp ienv))
	  (let ((first (car body)) (rest (cdr body)))
	    (let* ((head (and (pair? first) (not (id? first)) (car first)))
		   (head-val (and (id? head) (cdr (ienv head))))
		   (special (and (marked? head-val) (unmark head-val))))
	      (if (procedure? special)
		  (loop ienv vars inits (cons (special first ienv) rest))
		  (case special
		    ((begin) (loop ienv vars inits (append (cdr first) rest)))
		    ((def) (loop (env-add (cadr first) 'undefined ienv)
				 (cons (cadr first) vars)
				 (cons (caddr first) inits)
				 rest))
		    (else (for-each set-cdr! (map ienv vars) (map ieval inits))
			  (eval-begin body ienv)))))))))

    ;; We make a copy of the initial input to ensure that subsequent
    ;; mutation of it does not affect eval's result. [1]
    (lambda (initial-sexp env)
      (xeval (let copy ((x initial-sexp))
	       (cond ((string? x) (string-copy x))
		     ((pair? x) (cons (copy (car x)) (copy (cdr x))))
		     ((vector? x) (list->vector (copy (vector->list x))))
		     (else x)))
	     (or env (make-builtins-env))))))


(define null-environment
  (let ()
    (define (syntax-rules** id? new-id top-env ellipsis)
      (lambda (mac-env pat-literals rules)
        (define (pat-literal? id)     (memq id pat-literals))
	(define (not-pat-literal? id) (not (pat-literal? id)))
	(define (spair? x)            (and (pair? x) (not (id? x))))
	(define (ellipsis? x)         (and (id? x) (eq? (mac-env x)
							(top-env ellipsis))))
	(define (ellipsis-pair? x)    (and (spair? x) (ellipsis? (car x))))

	;; List-ids returns a list of the non-ellipsis ids in a
	;; pattern or template for which (pred? id) is true.  If
	;; include-scalars is false, we only include ids that are
	;; within the scope of at least one ellipsis.
	(define (list-ids x include-scalars pred?)
	  (let collect ((x x) (inc include-scalars) (l '()))
	    (cond ((id? x) (if (and inc (pred? x)) (cons x l) l))
		  ((vector? x) (collect (vector->list x) inc l))
		  ((pair? x)
		   (if (ellipsis-pair? (cdr x))
		       (collect (car x) #t (collect (cddr x) inc l))
		       (collect (car x) inc (collect (cdr x) inc l))))
		  (else l))))
    
	;; Returns #f or an alist mapping each pattern var to a part of
	;; the input.  Ellipsis vars are mapped to lists of parts (or
	;; lists of lists...).
	(define (match-pattern pat use env)
	  (call-with-current-continuation
	    (lambda (return)
	      (define (fail) (return #f))
	      (let match ((pat (cdr pat)) (sexp (cdr use)) (bindings '()))
		(define (continue-if condition) (if condition bindings (fail)))
		(cond
		 ((id? pat) (if (pat-literal? pat)
				(continue-if (and (id? sexp) (eq? (mac-env pat)
								  (env sexp))))
				(cons (cons pat sexp) bindings)))
		 ((id? sexp) (fail))
		 ((vector? pat)
		  (or (vector? sexp) (fail))
		  (match (vector->list pat) (vector->list sexp) bindings))
		 ((not (pair? pat)) (continue-if (equal? pat sexp)))
		 ((ellipsis-pair? (cdr pat))
		  (let slist? ((x sexp))
		    (or (null? x) (if (spair? x) (slist? (cdr x)) (fail))))
		  (let ((vars (list-ids pat #t not-pat-literal?)))
		    (define (match1 sexp) (map cdr (match (car pat) sexp '())))
		    (append (apply map list vars (map match1 sexp))
			    bindings)))
		 ((pair? sexp) (match (car pat) (car sexp)
				      (match (cdr pat) (cdr sexp) bindings)))
		 (else (fail)))))))

	(define (expand-template pat tmpl top-bindings)
	  ;; New-literals is an alist mapping each literal id in the
	  ;; template to a fresh id for inserting into the output.  It
	  ;; might have duplicate entries mapping an id to two different
	  ;; fresh ids, but that's okay because when we go to retrieve a
	  ;; fresh id, assq will always retrieve the first one.
	  (define new-literals
	    (map (lambda (id) (cons id (new-id (mac-env id))))
		 (list-ids tmpl #t (lambda (id)
				     (not (assq id top-bindings))))))
	  (define ellipsis-vars (list-ids (cdr pat) #f not-pat-literal?))
	  (define (list-ellipsis-vars subtmpl)
	    (list-ids subtmpl #t (lambda (id) (memq id ellipsis-vars))))
	  (let expand ((tmpl tmpl) (bindings top-bindings))
	    (let expand-part ((tmpl tmpl))
	      (cond
	       ((id? tmpl) (cdr (or (assq tmpl bindings)
				    (assq tmpl top-bindings)
				    (assq tmpl new-literals))))
	       ((vector? tmpl)
		(list->vector (expand-part (vector->list tmpl))))
	       ((pair? tmpl)
		(if (ellipsis-pair? (cdr tmpl))
		    (let ((vars-to-iterate (list-ellipsis-vars (car tmpl))))
		      (define (lookup var) (cdr (assq var bindings)))
		      (define (expand-car . vals)
			(expand (car tmpl) (map cons vars-to-iterate vals)))
		      (append (apply map expand-car
				     (map lookup vars-to-iterate))
			      (expand-part (cddr tmpl))))
		    (cons (expand-part (car tmpl)) (expand-part (cdr tmpl)))))
	       (else tmpl)))))

	(lambda (use env)
	  (let loop ((rules rules))
	    (let* ((rule (car rules)) (pat (car rule)) (tmpl (cadr rule)))
	      (cond ((match-pattern pat use env) =>
		     (lambda (bindings) (expand-template pat tmpl bindings)))
		    (else (loop (cdr rules)))))))))
    (define macro-defs
      '((define-syntax quote
	  (syntax-rules ()
	    ('(x . y) (cons 'x 'y))
	    ('#(x ...) (list->vector '(x ...)))
	    ('x (q x))))
	(define-syntax quasiquote
	  (syntax-rules (unquote unquote-splicing quasiquote)
	    (`,x x)
	    (`(,@x . y) (append x `y))
	    ((_ `x . d) (cons 'quasiquote       (quasiquote (x)   d)))
	    ((_ ,x   d) (cons 'unquote          (quasiquote (x) . d)))
	    ((_ ,@x  d) (cons 'unquote-splicing (quasiquote (x) . d)))
	    ((_ (x . y) . d)
	     (cons (quasiquote x . d) (quasiquote y . d)))
	    ((_ #(x ...) . d)
	     (list->vector (quasiquote (x ...) . d)))
	    ((_ x . d) 'x)))
	(define-syntax do
	  (syntax-rules ()
	    ((_ ((var init . step) ...)
		ending
		expr ...)
	     (let loop ((var init) ...)
	       (cond ending (else expr ... (loop (begin var . step) ...)))))))
	(define-syntax letrec
	  (syntax-rules ()
	    ((_ ((var init) ...) . body)
	     (let () (def var init) ... (let () . body)))))
	(define-syntax let*
	  (syntax-rules ()
	    ((_ () . body) (let () . body))
	    ((_ (first . more) . body)
	     (let (first) (let* more . body)))))
	(define-syntax let
	  (syntax-rules ()
	    ((_ ((var init) ...) . body)
	     ((lambda (var ...) . body)
	      init ...))
	    ((_ name ((var init) ...) . body)
	     ((letrec ((name (lambda (var ...) . body)))
		name)
	      init ...))))
	(define-syntax case
	  (syntax-rules ()
	    ((_ x (test . exprs) ...)
	     (let ((key x))
	       (cond ((case-test key test) . exprs)
		     ...)))))
	(define-syntax case-test
	  (syntax-rules (else) ((_ k else) #t) ((_ k atoms) (memv k 'atoms))))
	(define-syntax cond
	  (syntax-rules (else =>)
	    ((_) #f)
	    ((_ (else . exps)) (begin #f . exps))
	    ((_ (x) . rest) (or x (cond . rest)))
	    ((_ (x => proc) . rest)
	     (let ((tmp x)) (cond (tmp (proc tmp)) . rest)))
	    ((_ (x . exps) . rest)
	     (if x (begin . exps) (cond . rest)))))
	(define-syntax and
	  (syntax-rules ()
	    ((_) #t)
	    ((_ test) test)
	    ((_ test . tests) (if test (and . tests) #f))))
	(define-syntax or
	  (syntax-rules ()
	    ((_) #f)
	    ((_ test) test)
	    ((_ test . tests) (let ((x test)) (if x x (or . tests))))))
	(define-syntax define
	  (syntax-rules ()
	    ((_ (var . args) . body)
	     (define var (lambda args . body)))
	    ((_ var init) (def var init))))
	(define-syntax if
	  (syntax-rules () ((_ x y ...) (if* x (lambda () y) ...))))
	(define-syntax delay
	  (syntax-rules () ((_ x) (delay* (lambda () x)))))))
    (define (if* a b . c) (if a (b) (if (pair? c) ((car c)))))
    (define (delay* thunk) (delay (thunk)))
    (define (null-env)
      ((eval `(lambda (cons append list->vector memv delay* if* syntax-rules**)
		(def syntax-rules*
		     (syntax-rules** id? new-id (get-env) (syntax ...)))
		(def define-syntax def)
		((lambda ()
		   (define-syntax syntax-rules
		     (macro (syntax-rules*
			      (get-env)
			      (syntax ())
			      (syntax (((_ lits . rules)
					(macro (syntax-rules*
						 (get-env)
						 (syntax lits)
						 (syntax rules)))))))))
		   ((lambda ()
		      ,@macro-defs
		      (let ((let-syntax let) (letrec-syntax letrec))
			(get-env)))))))
	     #f)
       cons append list->vector memv delay* if* syntax-rules**))
    (define promise (delay (null-env)))
    (lambda (version)
      (if (= version 5)
          (force promise)
          (open-input-file "sheep-herders/r^-1rs.ltx")))))


(define scheme-report-environment
  (let-syntax
      ((extend-env
	(syntax-rules ()
	  ((_ env . names)
	   ((eval '(lambda names (get-env)) env)
	    . names)))))
    (let ()
      (define (r5-env)
	(extend-env (null-environment 5)
	  eqv? eq? equal?
	  number? complex? real? rational? integer? exact? inexact?
	  = < > <= >= zero? positive? negative? odd? even?
	  max min + * - /
	  abs quotient remainder modulo gcd lcm numerator denominator
	  floor ceiling truncate round rationalize
	  exp log sin cos tan asin acos atan sqrt expt
	  make-rectangular make-polar real-part imag-part magnitude angle
	  exact->inexact inexact->exact
	  number->string string->number
	  not boolean?
	  pair? cons car cdr set-car! set-cdr! caar cadr cdar cddr
	  caaar caadr cadar caddr cdaar cdadr cddar cdddr
	  caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
	  cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr
	  null? list? list length append reverse list-tail list-ref
	  memq memv member assq assv assoc
	  symbol? symbol->string string->symbol
	  char? char=? char<? char>? char<=? char>=?
	  char-ci=? char-ci<? char-ci>? char-ci<=? char-ci>=?
	  char-alphabetic? char-numeric? char-whitespace?
	  char-upper-case? char-lower-case?
	  char->integer integer->char char-upcase char-downcase
	  string? make-string string string-length string-ref string-set!
	  string=? string-ci=? string<? string>? string<=? string>=?
	  string-ci<? string-ci>? string-ci<=? string-ci>=?
	  substring string-append string->list list->string
	  string-copy string-fill!
	  vector? make-vector vector vector-length vector-ref vector-set!
	  vector->list list->vector vector-fill!
	  procedure? apply map for-each force
	  call-with-current-continuation
	  values call-with-values dynamic-wind
	  eval scheme-report-environment null-environment
	  call-with-input-file call-with-output-file
	  input-port? output-port? current-input-port current-output-port
	  with-input-from-file with-output-to-file
	  open-input-file open-output-file close-input-port close-output-port
	  read read-char peek-char eof-object? char-ready?
	  write display newline write-char))
      (define promise (delay (r5-env)))
      (lambda (version)
	(if (= version 5)
	    (force promise)
	    (open-input-file "sheep-herders/r^-1rs.ltx"))))))

;; [1] Some claim that this is not required, and that it is compliant for
;;
;;   (let* ((x (string #\a))
;;          (y (eval x (null-environment 5))))
;;     (string-set! x 0 #\b)
;;     y)
;;
;; to return "b", but I say that's as bogus as if
;;
;;   (let* ((x (string #\1))
;;          (y (string->number x)))
;;     (string-set! x 0 #\2)
;;     y)
;;
;; returned 2.  Most implementations disagree with me, however.
;;
;; Note: it would be fine to pass through those strings (and pairs and
;; vectors) that are immutable, but we can't portably detect them.


;; Repl provides a simple read-eval-print loop.  It semi-supports
;; top-level definitions and syntax definitions, but each one creates
;; a new binding whose region does not include anything that came
;; before the definition, so if you want mutually recursive top-level
;; procedures, you have to do it the hard way:
;;   (define f #f)
;;   (define (g) (f))
;;   (set! f (lambda () (g)))
;; Repl does not support macro uses that expand into top-level definitions.
(define (repl)
  (let repl ((env (scheme-report-environment 5)))
    (display "eiod> ")
    (let ((exp (read)))
      (if (not (eof-object? exp))
	  (case (and (pair? exp) (car exp))
	    ((define define-syntax) (repl (eval `(let () ,exp (get-env))
						env)))
	    (else
	     (for-each (lambda (val) (write val) (newline))
		       (call-with-values (lambda () (eval exp env))
			 list))
	     (repl env)))))))

(define (tests noisy)
  (define env (scheme-report-environment 5))
  (for-each
   (lambda (x)
     (let* ((exp (car x))
	    (expected (cadr x)))
       (if noisy (begin (display "Trying: ") (write exp) (newline)))
       (let* ((result (eval exp env))
	      (success (equal? result expected)))
	 (if (not success) 
	     (begin (display "Failed: ")
		    (if (not noisy) (write exp))
		    (display " returned ")
		    (write result)
		    (display ", not ")
		    (write expected)
		    (newline))))))
   '((1 1)
     (#t #t)
     ("hi" "hi")
     (#\a #\a)
     ('1 1)
     ('foo foo)
     ('(a b) (a b))
     ('#(a b) #(a b))
     (((lambda (x) x) 1) 1)
     ((+ 1 2) 3)
     (((lambda (x) (set! x 2) x) 1) 2)
     (((lambda () (define x 1) x)) 1)
     (((lambda () (define (x) 1) (x))) 1)
     ((begin 1 2) 2)
     (((lambda () (begin (define x 1)) x)) 1)
     (((lambda () (begin) 1)) 1)
     ((let-syntax ((f (syntax-rules () ((_) 1)))) (f)) 1)
     ((letrec-syntax ((f (syntax-rules () ((_) (f 1)) ((_ x) x)))) (f)) 1)
     ((let-syntax ((f (syntax-rules () ((_ x ...) '(x ...))))) (f 1 2)) (1 2))
     ((let-syntax ((f (syntax-rules ()
			((_ (x y) ...) '(x ... y ...))
			((_ x ...) '(x ...)))))
	(f (x1 y1) (x2 y2)))
      (x1 x2 y1 y2))
     ((let-syntax ((let (syntax-rules ()
			  ((_ ((var init) ...) . body)
			   '((lambda (var ...) . body) init ...)))))
	(let ((x 1) (y 2)) (+ x y)))
      ((lambda (x y) (+ x y)) 1 2))
     ((let ((x 1)) x) 1)
     ((let* ((x 1) (x (+ x 1))) x) 2)
     ((let ((call/cc call-with-current-continuation))
	(letrec ((x (call/cc list)) (y (call/cc list)))
	  (if (procedure? x) (x (pair? y))) 
	  (if (procedure? y) (y (pair? x)))
	  (let ((x (car x)) (y (car y)))
	    (and (call/cc x) (call/cc y) (call/cc x)))))
      #t)
     ((if 1 2) 2)
     ((if #f 2 3) 3)
     ((force (delay 1)) 1)
     ((let* ((x 0) (p (delay (begin (set! x (+ x 1)) x)))) (force p) (force p))
      1)
     ((let-syntax
	  ((foo (syntax-rules ()
		  ((_ (x ...) #(y z ...) ...)
		   '((z ...) ... #((x y) ...))))))
	(foo (a b c) #(1 i j) #(2 k l) #(3 m n)))
      ((i j) (k l) (m n) #((a 1) (b 2) (c 3))))
     ((do ((vec (make-vector 5))
	   (i 0 (+ i 1)))
	  ((= i 5) vec)
	(vector-set! vec i i))
      #(0 1 2 3 4))
     ((let-syntax ((f (syntax-rules (x) ((_ x) 1) ((_ y) 2))))
	(define x (f x))
	x)
      2))))

;; matching close paren for quote-and-evaluate at beginning of file.
) 

