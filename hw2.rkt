#lang racket

(require racket/trace)
(require racket/format)
(require "hw1.rkt")

(provide interpret)
(provide tm-interpreter)
(provide interpret-expr)
(provide first-futamura)
(provide tm-example)
(provide tm-example-1)
(provide pretty-print)
(provide second-futamura-bad)

(provide the-mix)
(provide first-futamura-new)
(provide second-futamura)

(provide filter-vars)
(provide create-label)
(provide is-static)
(provide reduce)
(provide quote-res)
(provide down)
(provide list-to-val)
(provide my-trace)

(define (create-label pp vs)
  `(,pp . ,vs)
  )

(define (quote-res l) (cons 'quote (list l)))

(define (reduce expr vs)
  (match expr
    [`(quote . ,args) expr]
    [`(if . ,args) (list 'if (reduce (car args) vs) (reduce (car (cdr args)) vs) (reduce (car (cdr (cdr args))) vs))]
    [`(,op . ,args) (let ([real-args (map (lambda (arg) (reduce arg vs)) args)])
                      (cons op real-args))]
    [`,x (let ([found (hash-has-key? vs x)])
              (if found (quote-res (hash-ref vs x)) x))])
  )

;(trace reduce)

(define (is-static expr static)
  (match expr
    [`(quote . ,args) #t]
    [`(if . ,args) (foldl (lambda (x y) (and y (is-static x static))) #t args)]
    [`(,op . ,args) (foldl (lambda (x y) (and y (is-static x static))) #t args)]
    [`,x (if (not (member x static)) #f #t)])
  )
  
;(trace is-static)

(define (filter-vars read static) (filter (lambda (arg) (not (member arg static))) read))

(define (list-to-val l)
  (match l
    [`(,x) x]
    [_ l]))

(define (down l) (map (lambda (arg) (cons (car arg) (list-to-val (cdr arg)))) l))

(define (mix) '((read program division vs0)
                (pre-main (pending := list->set (list (cons (car (car (cdr program))) (make-immutable-hash vs0))))
                          (static := car division)
                          (dynamic := cdr division)
                          (residual := list (filter-vars (car program) static))
                          (program := make-immutable-hash (cdr program))
                          (marked := list->set ())
                          (goto while-pending))
                (while-pending (if (set-empty? pending) goto exit goto body-pending))
                (body-pending (ppvs := set-first pending)
                              (pending := set-rest pending)
                              (pp := car ppvs)
                              (vs := cdr ppvs)
                              (marked := set-add marked ppvs)
                              (bb := hash-ref program pp ())
                              (code := cons (create-label pp vs) ())
                              (goto while-bb))
                (end-pending (residual := append residual (list code))
                             (goto while-pending))
                (while-bb (if (null? bb) goto end-pending goto body-bb))
                (body-bb (command := car bb)
                         (bb := cdr bb)
                         (goto case-assign))
                (case-assign (if (equal? (second command) ':=) goto process-assign goto case-goto))
                (process-assign (if (is-static (car command) static) goto update-vs goto extend-code-assign))
                (update-vs (vs := hash-set vs (car command) (interpret-expr (hash->list vs) (list-to-val (cdr (cdr command)))))
                           (goto while-bb))
                (extend-code-assign (code := append code (list (append (list (car command) :=) (reduce (list-to-val (cdr (cdr command))) vs))))
                                    (goto while-bb))
                (case-goto (if (equal? (car command) 'goto) goto process-goto goto case-if))
                (process-goto (bb := hash-ref program (cadr command) ())
                              (goto while-bb))
                (case-if (if (equal? (car command) 'if) goto process-if goto case-return))
                (process-if (if (is-static (second command) static) goto static-conditional goto dynamic-conditional))
                (static-conditional (pp-quote := hash-ref program (fourth command) ())
                                    (pp-quote-quote := hash-ref program (sixth command) ())
                                    (if (interpret-expr (hash->list vs) (second command)) goto static-pp-quote goto static-pp-quote-quote))
                (static-pp-quote (bb := pp-quote)
                                 (goto while-bb))
                (static-pp-quote-quote (bb := pp-quote-quote)
                                       (goto while-bb))
                (dynamic-conditional (pending := set-subtract
                                              (set-union pending (list->set (list (cons (fourth command) vs) (cons (sixth command) vs))))
                                              marked)
                                     (code := append code (list (append
                                                           (append (list if) (list (reduce (second command) vs)))
                                                           (list goto (create-label (fourth command) vs) goto (create-label (sixth command) vs))
                                                           )))
                                     (goto while-bb))
                (case-return (if (equal? (car command) 'return) goto process-return goto process-error))
                (process-return (code := append code (list (append (list return) (reduce (cdr command) vs))))
                                (goto while-bb))
                (process-error (return error "Mix: unknown expression"))
                (exit (return residual))
                ))

(define (my-trace x y) x)
(trace my-trace)

(define (pretty-print-block block map-of-names)
  (let ([new-name (hash-ref map-of-names (car block))]
        [new-last (map (lambda (arg) (if (hash-has-key? map-of-names arg) (hash-ref map-of-names arg) arg)) (last block))]
       ) (cons new-name (append (reverse (cdr (reverse (cdr block)))) (list new-last))))
)

(define (pretty-print program)
  (let ([read-block (car program)]
        [names (map (lambda (arg) (car arg)) (cdr program))]
        [new-names (map (lambda (arg) (string-append "label" (~v arg))) (stream->list (in-range 0 (length (cdr program)) 1)))])
       (let ([map-of-names (make-immutable-hash (zip names new-names))])
        (cons read-block (map (lambda (arg) (pretty-print-block arg map-of-names)) (cdr program)))))
)

;(interpret (mix) (list (assign-program) (cons '(y) '(x)) (list (cons 'y 42)))) — '((main #hash((x . +) (y . 42))) (return x))
;(interpret (mix) (list (find-name) (cons '(name namelist) '(valuelist)) (list (cons 'name 'alex) (cons 'namelist '(al al alex ke a))))) — ((read valuelist) ((search #hash((name . alex) (namelist . (al al alex ke a)))) (valuelist := cdr valuelist) (valuelist := cdr valuelist) (return car valuelist)))


(define (assign-program)
  '((read x y)
    (main (x := + x y)
          (return x))))

(define (find-name) '((read name namelist valuelist)
                      (search (if (equal? name (car namelist)) goto found goto cont))
                      (cont (valuelist := cdr valuelist)
                            (namelist := cdr namelist)
                            (goto search))
                      (found (return car valuelist))
                     ))

(define (tm-example) '((left)
                      (left)
                      (write 1)
                      (if 1 goto 4)
                      (if 0 goto 1)
                      (write 0)
                      (if 0 goto 7)
                      (right)
                      (left)
                      (right)
                      (right)
                      (write 1)
                      (if 1 goto 13)
                      (goto 14)
                      (right)
                      (left)
                      (left)
                      (left)
                      (write 0)))
                      
(define (tm-example-1) '((if 0 goto 3)
                        (right)
                        (goto 0)
                        (write 1)))

; Task 2
(define (first-futamura program) (pretty-print (interpret (mix) (list
                                                   (tm-interpreter)
                                                   (cons '(Q Qtail Instruction Operator Symbol NextLabel) '(Right Left))
                                                   (list (cons 'Q program))))))
; Example of usage:
;   compiling program        — (define (mixed) (first-futamura (tm-example-1)))
;   compiled program itslef  — (mixed)
;   running compiled program — (interpret (mixed) '((1 1 0 1 1)))

; Task 3                                               
(define (second-futamura-bad) (pretty-print (interpret (mix) (list
                                             (mix)
                                             (cons '(program division static dynamic) '(pending marked residual ppvs pp vs vs0 bb code command pp-quote pp-quote-quote))
                                             (list (cons 'program (tm-interpreter))
                                                   (cons 'division (cons '(Q Qtail Instruction Operator Symbol NextLabel) '(Right Left))))))))             

; Bad (without "The Trick") II Futamura projection really compiles programs the same way as I projection: 
;  (pretty-print (interpret (second-futamura-bad) (list (list (cons 'Q (tm-example-1))))))
; Bad (without "The Trick") II Futamura projection compiler produces programs that give accurate result: 
;  (interpret (interpret (second-futamura-bad) (list (list (cons 'Q (tm-example-1))))) '((1 1 0 1 1)))

; Task 4

(define (the-mix) '((read program division vs0)
                (pre-main (pending := list->set (list (create-label (car (car (cdr program))) (make-immutable-hash vs0))))
                          (static := car division)
                          (dynamic := cdr division)
                          (residual := list (filter-vars (car program) static))
                          (program := make-immutable-hash (cdr program))
                          (program-old-tmp := hash->list program)
                          (marked := list->set ())
                          (goto while-pending))
                (while-pending (if (set-empty? pending) goto exit goto body-pending))
                (body-pending (ppvs := set-first pending)
                              (pending := set-rest pending)
                              (pp := car ppvs)
                              (vs := cdr ppvs)
                              (marked := set-add marked ppvs)
                              (next-c := 'body-pending1)
                              (goto find-pp))
                (find-pp (if (null? program-old-tmp) goto error-exit goto find-pp-inner))
                (find-pp-inner (pp-tmp := car (car (program-old-tmp)))
                               (bb := cdr (car (program-old-tmp)))
                               (program-old-tmp := cdr program-old-tmp)
                               (if (equal? pp pp-tmp) goto next goto find-pp))
                (next (program-old-tmp := hash->list program)
                      (if (equal? next-c 'while-bb) goto while-bb goto body-pending1))
                (body-pending1 (code := cons (create-label pp vs) ())
                               (goto while-bb))
                (end-pending (residual := append residual (list code))
                             (goto while-pending))
                (while-bb (if (null? bb) goto end-pending goto body-bb))
                (body-bb (command := car bb)
                         (bb := cdr bb)
                         (goto case-assign))
                (case-assign (if (equal? (second command) ':=) goto process-assign goto case-goto))
                (process-assign (if (is-static (car command) static) goto update-vs goto extend-code-assign))
                (update-vs (vs := hash-set vs (car command) (interpret-expr (hash->list vs) (list-to-val (cdr (cdr command)))))
                           (goto while-bb))
                (extend-code-assign (code := append code (list (append (list (car command) :=) (reduce (list-to-val (cdr (cdr command))) vs))))
                                    (goto while-bb))
                (case-goto (if (equal? (car command) 'goto) goto process-goto goto case-if))
                (process-goto (next-c := 'while-bb)
                              (pp := cadr command)
                              (goto find-pp))
                (case-if (if (equal? (car command) 'if) goto process-if goto case-return))
                (process-if (if (is-static (second command) static) goto static-conditional goto dynamic-conditional))
                (static-conditional (if (interpret-expr (hash->list vs) (second command)) goto static-pp-quote goto static-pp-quote-quote))
                (static-pp-quote (next-c := 'while-bb)
                                 (pp := fourth command)
                                 (goto find-pp))
                (static-pp-quote-quote (next-c := 'while-bb)
                                       (pp := sixth command)
                                       (goto find-pp))
                (dynamic-conditional (pending := set-subtract
                                              (set-union pending (list->set (list (create-label (fourth command) vs) (create-label (sixth command) vs))))
                                              marked)
                                     ; (pp-tmp := my-trace pp-tmp (list (length (set->list (set-subtract (list->set (list (create-label (fourth command) vs) (create-label (sixth command) vs))) marked))) (fourth command) (sixth command) (list (if (hash-has-key? vs 'pp-tmp) (hash-ref vs 'pp-tmp) '()) (if (hash-has-key? vs 'next-c) (hash-ref vs 'next-c) '()) (if (hash-has-key? vs 'command) (hash-ref vs 'command) '()) (if (hash-has-key? vs 'bb) (hash-ref vs 'bb) '()))))
                                     (code := append code (list (append
                                                           (append (list if) (list (reduce (second command) vs)))
                                                           (list goto (create-label (fourth command) vs) goto (create-label (sixth command) vs))
                                                           )))
                                     (goto while-bb))
                (case-return (if (equal? (car command) 'return) goto process-return goto process-error))
                (process-return (code := append code (list (append (list return) (reduce (cdr command) vs))))
                                (goto while-bb))
                (process-error (return error "Mix: unknown expression"))
                (exit (return residual))
                (error-exit (return 'error))
                ))
                
; (trace reduce)

(define (first-futamura-new program) (pretty-print (interpret (the-mix) (list
                                                   (tm-interpreter)
                                                   (cons '(Q Qtail Instruction Operator Symbol NextLabel) '(Right Left))
                                                   (list (cons 'Q program))))))
                                                   
(define (second-futamura) (pretty-print (interpret (the-mix) (list
                                             (the-mix)
                                             (cons '(program division static dynamic bb next-c command pp-tmp program-old-tmp) '(pending marked residual ppvs pp vs vs0 code))
                                             (list (cons 'program (tm-interpreter))
                                                   (cons 'division (cons '(Q Qtail Instruction Operator Symbol NextLabel) '(Right Left)))))))) 

; Example of usage:
;   compiling program        — (define (mixed) (first-futamura-new (tm-example-1)))
;   compiled program itslef  — (mixed)
;   running compiled program — (interpret (mixed) '((1 1 0 1 1)))   
                                          
; NOTE: the code below really works, but produced compiler has around 360 labels
;       and its generation time is approximately 5 mins. It looks like there's
;       an error somewhere concerning visiting pending blocks that SHOULD HAVE BEEN
;       marked, but somehow they weren't marked.
; II Futamura projection really compiles programs the same way as I projection: 
;  (pretty-print (interpret (second-futamura) (list (list (cons 'Q (tm-example-1))))))
; II Futamura projection compiler produces programs that give accurate result: 
;  (interpret (interpret (second-futamura) (list (list (cons 'Q (tm-example-1))))) '((1 1 0 1 1)))