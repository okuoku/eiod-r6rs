;; eiod.scm: eval-in-one-define
;; Copyright 2002 Al Petrofsky <al@petrofsky.org>
;;
;; A minimal implementation of r5rs eval, null-environment, and
;; scheme-report-environment.

;; Data Structures:

;; An environment is an alist:

;; environment:    (proper-binding ...)
;; proper-binding: (identifier . [value | macro])
;; macro:          (procedure . marker)

;; A value is any arbitrary scheme value.  Macros are stored in pairs
;; whose cdr is the eq?-unique marker object.

;; identifier: [symbol | (binding . marker)]
;; binding:    [symbol | proper-binding]

;; When a template containing a literal identifier is expanded, the
;; identifier is replaced with a new pair containing the marker object
;; and the binding of the literal in the environment of the macro (or
;; the plain symbol if there is no binding).

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

    (define (id? sexp)    (or (symbol? sexp) (marked? sexp)))
    (define (spair? sexp) (and (pair? sexp) (not (marked? sexp))))

    (define (ids->syms sexp)
      (cond ((id? sexp) (let loop ((x sexp)) (if (pair? x) (loop (car x)) x)))
	    ((pair? sexp) (cons (ids->syms (car sexp)) (ids->syms (cdr sexp))))
	    ((vector? sexp) (list->vector (ids->syms (vector->list sexp))))
	    (else sexp)))
    
    (define (lookup id env)
      (or (assq id env) (if (symbol? id) id (unmark id))))

    (define (acons key val alist) (cons (cons key val) alist))

    (define (xeval sexp env)
      (let eval-in-this-env ((sexp sexp))
	(cond ((id? sexp) (cdr (lookup sexp env)))
	      ((not (spair? sexp)) sexp)
	      (else
	       (let ((head (car sexp)) (tail (cdr sexp)))
		 (let ((binding (and (id? head) (lookup head env))))
		   (case binding
		     ((get-env) env)
		     ((quote)   (ids->syms (car tail)))
		     ((begin)   (eval-begin tail env))
		     ((lambda)  (eval-lambda tail env))
		     ((set!)    (set-cdr! (lookup (car tail) env)
					  (eval-in-this-env (cadr tail))))
		     ((syntax-rules) (eval-syntax-rules tail env))
		     (else (let ((val (and binding (cdr binding))))
			     (if (marked? val)
				 (eval-in-this-env ((unmark val) tail env))
				 (apply (eval-in-this-env head)
					(map eval-in-this-env tail))))))))))))

    (define (eval-begin tail env)
      ;; Don't use for-each because we must tail-call the last expression.
      (do ((sexp1 (car tail) (car sexps))
	   (sexps (cdr tail) (cdr sexps)))
	  ((null? sexps) (xeval sexp1 env))
	(xeval sexp1 env)))

    (define (eval-lambda tail env)
      (lambda args
	(define ienv (do ((args args (cdr args))
			  (vars (car tail) (cdr vars))
			  (env env (acons (car vars) (car args) env)))
			 ((not (spair? vars))
			  (if (null? vars) env (acons vars args env)))))
	(let loop ((ienv ienv) (def-tails '()) (body (cdr tail)))
	  (define (finish)
	    (for-each (lambda (var val) (set-cdr! (lookup var ienv) val))
		      (map car def-tails)
		      (map (lambda (def-tail) (xeval (cadr def-tail) ienv))
			   def-tails))
	    (eval-begin body ienv))
	  (define rest (cdr body))
	  (let retry ((sexp (car body)))
	    (if (not (spair? sexp))
		(finish)
		(let ((head (car sexp)) (tail (cdr sexp)))
		  (let ((binding (and (id? head) (lookup head ienv))))
		    (case binding
		      ((begin) (loop ienv def-tails (append tail rest)))
		      ((define) (loop (acons (car tail) #f ienv)
				      (cons tail def-tails)
				      rest))
		      (else (let ((val (and (pair? binding) (cdr binding))))
			      (if (marked? val)
				  (retry ((unmark val) tail ienv))
				  (finish))))))))))))

    (define (eval-syntax-rules mac-tail mac-env)
      (define literals (car mac-tail))
      (define rules    (cdr mac-tail))

      (define (pat-literal? id)     (memq id literals))
      (define (not-pat-literal? id) (not (pat-literal? id)))

      (define (ellipsis? x)      (and (id? x) (eq? '... (lookup x mac-env))))
      (define (ellipsis-pair? x) (and (spair? x) (ellipsis? (car x))))

      ;; List-ids returns a list of those ids in a pattern or template
      ;; for which (pred? id) is true.  If include-scalars is false, we
      ;; only include ids that are within the scope of at least one
      ;; ellipsis.
      (define (list-ids x include-scalars pred?)
	(let collect ((x x) (including include-scalars) (l '()))
	  (cond ((vector? x) (collect (vector->list x) including l))
		((and (id? x) including (pred? x))
		 (cons x l))
		((spair? x)
		 (if (ellipsis-pair? (cdr x))
		     (collect (car x) #t
			      (collect (cddr x) including l))
		     (collect (car x) including
			      (collect (cdr x) including l))))
		(else l))))
    
      ;; Returns #f or an alist mapping each pattern var to a part of
      ;; the input.  Ellipsis vars are mapped to lists of parts (or
      ;; lists of lists...).
      (define (match-pattern pat tail env)
	(call-with-current-continuation
	 (lambda (return)
	   (define (fail) (return #f))
	   (let match ((pat (cdr pat)) (sexp tail) (bindings '()))
	     (define (continue-if condition) (if condition bindings (fail)))
	     (cond
	      ((id? pat)
	       (if (pat-literal? pat)
		   (continue-if (and (id? sexp) (eq? (lookup pat mac-env)
						     (lookup sexp env))))
		   (acons pat sexp bindings)))
	      ((vector? pat)
	       (or (vector? sexp) (fail))
	       (match (vector->list pat) (vector->list sexp) bindings))
	      ((not (spair? pat))
	       (continue-if (equal? pat sexp)))
	      ((ellipsis-pair? (cdr pat))
	       (or (list? sexp) (fail))
	       (append (apply map list (list-ids pat #t not-pat-literal?)
			      (map (lambda (x)
				     (map cdr (match (car pat) x '())))
				   sexp))
		       bindings))
	      ((spair? sexp)
	       (match (car pat) (car sexp)
		      (match (cdr pat) (cdr sexp) bindings)))
	      (else (fail)))))))

      (define (expand-template pat tmpl top-bindings)
	(define ellipsis-vars (list-ids pat #f not-pat-literal?))
	(define (list-ellipsis-vars subtmpl)
	  (list-ids subtmpl #t (lambda (id) (memq id ellipsis-vars))))
	;; New-literals is an alist mapping each literal id in the
	;; template to a fresh id for inserting into the output.  It
	;; might have duplicate entries mapping an id to two different
	;; fresh ids, but that's okay because when we go to retrieve a
	;; fresh id, assq will always retrieve the first one.
	(define new-literals
	  (map (lambda (id) (cons id (mark (lookup id mac-env))))
	       (list-ids tmpl #t (lambda (id) (not (assq id top-bindings))))))
	(let expand ((tmpl tmpl) (bindings top-bindings))
	  (let expand-part ((tmpl tmpl))
	    (cond
	     ((id? tmpl) (cdr (or (assq tmpl bindings)
				  (assq tmpl top-bindings)
				  (assq tmpl new-literals))))
	     ((vector? tmpl) (list->vector (expand-part (vector->list tmpl))))
	     ((spair? tmpl)
	      (if (ellipsis-pair? (cdr tmpl))
		  (let ((vars-to-iterate (list-ellipsis-vars (car tmpl))))
		    (append (apply map
				   (lambda vals
				     (expand (car tmpl)
					     (map cons vars-to-iterate vals)))
				   (map (lambda (var)
					  (cdr (assq var bindings)))
					vars-to-iterate))
			    (expand-part (cddr tmpl))))
		  (cons (expand-part (car tmpl)) (expand-part (cdr tmpl)))))
	     (else tmpl)))))

      (mark (lambda (tail env)
	      (let loop ((rules rules))
		(define rule (car rules))
		(let ((pat (car rule)) (tmpl (cadr rule)))
		  (define bindings (match-pattern pat tail env))
		  (if bindings
		      (expand-template pat tmpl bindings)
		      (loop (cdr rules))))))))

    ;; We make a copy of the initial input to ensure that subsequent
    ;; mutation of it does not affect eval's result. [1]
    (lambda (initial-sexp env)
      (xeval (let copy ((x initial-sexp))
	       (cond ((string? x) (string-copy x))
		     ((pair? x) (cons (copy (car x)) (copy (cdr x))))
		     ((vector? x) (list->vector (copy (vector->list x))))
		     (else x)))
	     env))))


(define null-environment
  (let ()
    (define macro-defs
      '((define quasiquote
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
	(define do
	  (syntax-rules ()
	    ((_ ((var init . step) ...)
		end-clause
		. commands)
	     (let loop ((var init) ...)
	       (cond end-clause
		     (else (begin #f . commands)
			   (loop (begin var . step) ...)))))))
	(define letrec
	  (syntax-rules ()
	    ((_ ((var init) ...) . body)
	     (let () (define var init) ... (let () . body)))))
	(define let*
	  (syntax-rules ()
	    ((_ () . body) (let () . body))
	    ((_ (first . more) . body)
	     (let (first) (let* more . body)))))
	(define let
	  (syntax-rules ()
	    ((_ ((var init) ...) . body)
	     ((lambda (var ...) . body)
	      init ...))
	    ((_ name ((var init) ...) . body)
	     ((letrec ((name (lambda (var ...) . body)))
		name)
	      init ...))))
	(define case
	  (syntax-rules (else)
	    ((_ (x . y) . clauses)
	     (let ((key (x . y)))
	       (case key . clauses)))
	    ((_ key (else . exps))
	     (begin #f . exps))
	    ((_ key (atoms . exps) . clauses)
	     (if (memv key 'atoms) (begin . exps) (case key . clauses)))
	    ((_ key) #f)))
	(define cond
	  (syntax-rules (else =>)
	    ((_) #f)
	    ((_ (else . exps)) (begin #f . exps))
	    ((_ (x) . rest) (or x (cond . rest)))
	    ((_ (x => proc) . rest)
	     (let ((tmp x)) (cond (tmp (proc tmp)) . rest)))
	    ((_ (x . exps) . rest)
	     (if x (begin . exps) (cond . rest)))))
	(define and
	  (syntax-rules ()
	    ((_) #t)
	    ((_ test) test)
	    ((_ test . tests) (if test (and . tests) #f))))
	(define or
	  (syntax-rules ()
	    ((_) #f)
	    ((_ test) test)
	    ((_ test . tests) (let ((x test)) (if x x (or . tests))))))
	(define if
	  (syntax-rules ()
	    ((_ a b)   (if* a (lambda () b)))
	    ((_ a b c) (if* a (lambda () b) (lambda () c)))))
	(define delay
	  (syntax-rules ()
	    ((_ x) (delay* (lambda () x)))))
	(define define-curried
	  (syntax-rules ()
	    ((_ (var . args) . body) (define-curried var (lambda args . body)))
	    ((_ var init) (define var init))))))
    (define (delay* thunk) (delay (thunk)))
    (define (if* a b . c) (if (null? c) (if a (b)) (if a (b) ((car c)))))
    (define (null-env)
      ((eval `(lambda (cons append list->vector memv delay* if*)
		,@macro-defs
		(let ((let-syntax let)
		      (letrec-syntax letrec)
		      (define define-curried))
		  (get-env)))
	     '())
       cons append list->vector memv delay* if*))
    (define promise (delay (null-env)))
    (lambda (version)
      (if (= version 5)
          (force promise)
          (open-input-file "sheep-herders/r^-1rs.ltx")))))


(define scheme-report-environment
  (let-syntax
      ((extend-env
	(syntax-rules ()
	  ((_ env name ...)
	   ((eval '(lambda (name ...) (get-env))
		  env)
	    name ...)))))
    (let ()
      (define (r5-env)
	(extend-env (null-environment 5)
	  eqv? eq? equal?
	  number? complex? real? rational? integer? exact? inexact?
	  = < > <= >= zero? positive? negative? odd? even?
	  max min + * - /
	  abs quotient remainder modulo gcd lcm ;; numerator denominator
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
;; a new binding, so if you want mutually recursive top-level
;; procedures, you have to do it the hard way:
;;   (define f #f)
;;   (define (g) (f))
;;   (set! f (lambda () (g)))
(define (repl)
  (let repl ((env (scheme-report-environment 5)))
    (display "eiod> ")
    (let ((exp (read)))
      (if (not (eof-object? exp))
	  (case (and (pair? exp) (car exp))
	    ((define define-syntax)
	     (repl (eval `(let () (define ,@(cdr exp)) (get-env))
			 env)))
	    (else
	     (write (eval exp env))
	     (newline)
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

