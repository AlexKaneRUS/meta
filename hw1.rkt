#lang racket

(require racket/trace)

(provide interpret)
(provide tm-interpreter)
(provide interpret-expr)
(provide tm-example)
(provide zip)

(define interpret
  (lambda (program data)
    (match program
      ['() (error "main: empty program")]
      [`(,read . ,blocks) (interpret-block (read-state read data) blocks (car blocks))])))

(define (zip lst1 lst2)
  (if (null? lst1)
      '()
      (cons (cons (car lst1) (car lst2))
            (zip (cdr lst1) (cdr lst2)))))

(define (read-state vars data)
  (match vars
    ['() '()]
    [`(read . ,t) (zip t data)]))   

(define (interpret-block state blocks block)
  (match block
    ['() (error "block: empty-block")]
    [`(,x . ,assignments-jump) (let ([new-state-block (interpret-assignments state assignments-jump)])
                                 (interpret-jump (car new-state-block) blocks (cdr new-state-block)))]))

(define (interpret-assignments state block)
  (match block
    [`((,x . (:= . ,y))) (list (assign '() state x (list-to-val y)) '())]
    [`((,x . (:= . ,y)) . ,ts) (interpret-assignments (assign '() state x (list-to-val y)) ts)]
    ['() (error "interpret-assignments: no jump after assignments")]
    [_ (cons state (if (list? (car block)) (car block) block))]))

(define (list-to-val l)
  (match l
    [`(,x) x]
    [_ l]))

(define (interpret-jump state blocks block)
  (match block
    [`(goto ,label) (find-and-go state blocks label)]
    [`(if ,expr goto ,then goto ,else) (if (interpret-expr state expr) (find-and-go state blocks then) (find-and-go state blocks else))]
    [`(return . ,expr) (interpret-expr state (list-to-val expr))]
    [_ (error "interpret-jump: no jumps found")]))

;(trace interpret-jump)

(define (find-and-go state blocks label)
  (let ([found (findf (lambda (arg) (equal? (car arg) label)) blocks)])
               (if found (interpret-block state blocks found) (error "interpret-jump: unknown block"))))

(define (assign bef-state state x y)
  (match state
    ['() (append bef-state (list (cons x (interpret-expr (append bef-state state) y))))]
    [`(,h . ,t) (if (equal? (car h) x) (append bef-state (cons (cons x (interpret-expr (append bef-state state) y)) t)) (assign (append bef-state (list h)) t x y))]))

(define (interpret-expr state e)
  (match e
      [`(if . ,args) (if (interpret-expr state (first args)) (interpret-expr state (second args)) (interpret-expr state (third args)))]
      [ `(,x) (let ([found (findf (lambda (arg) (equal? (car arg) x)) state)])
                (if found (cdr found) (list x)))]
      [`(quote . ,args) (list-to-val args)]
      [`(,op . ,args) (let ([real-args (map (lambda (arg) (quote-res (interpret-expr state arg))) args)])
                        (let ([real-e (cons op real-args)]) (eval real-e)))]
      [ `,x (let ([found (findf (lambda (arg) (equal? (car arg) x)) state)])
              (if found (cdr found) x))]))

;(trace interpret-expr)

(define (my-trace x) x)
(trace my-trace)

(define (quote-res l) (cons 'quote (list l)))

(define (find-name) '((read name namelist valuelist)
                      (search (if (equal? name (car namelist)) goto found goto cont))
                      (cont (valuelist := cdr valuelist)
                            (namelist := cdr namelist)
                            (goto search))
                      (found (return car valuelist))
                     ))

(define (tm-interpreter) '((read Q Right)
                           (init (Qtail := Q)
                                 (Left := '())
                                 (goto loop))
                           (loop (if (null? Qtail) goto stop goto cont))
                           (cont (Instruction := car Qtail)
                                 (Qtail := cdr Qtail)
                                 (Operator := car Instruction)
                                 (if (equal? Operator 'right) goto do-right goto cont1))
                           (cont1 (if (equal? Operator 'left) goto do-left goto cont2))
                           (cont2 (if (equal? Operator 'write) goto do-write goto cont3))
                           (cont3 (if (equal? Operator 'goto) goto do-goto goto cont4))
                           (cont4 (if (equal? Operator 'if) goto do-if goto error))
                           (do-right (Left := cons (car Right) Left)
                                     (Right := cdr Right)
                                     (goto loop))
                           (do-left (Right := cons (car Left) Right)
                                    (Left := cdr Left)
                                    (goto loop))
                           (do-write (Symbol := cadr Instruction)
                                     (Right := cons Symbol (cdr Right))
                                     (goto loop))
                           (do-goto (NextLabel := cadr Instruction)
                                    (Qtail := list-tail Q NextLabel)
                                    (goto loop))
                           (do-if (Symbol := cadr Instruction)
                                  (NextLabel := cadddr Instruction)
                                  (if (equal? Symbol (car Right)) goto jump goto loop))
                           (jump (Qtail := list-tail Q NextLabel)
                                 (goto loop))
                           (error (return ('syntaxerror: Instruction)))
                           (stop (return Right))
                          ))

(define (tm-example) '(((if 0 goto 3)
                        (right)
                        (goto 0)
                        (write 1)) (1 1 0 1 1)))

; example of running FlowChar: (interpret (find-name) '(alex (al al alx alex al) (0 3 2 1 4)))
; example of running Turing Machine: (interpret (tm-interpreter) (tm-example))
; (interpret (find-name) '("alex" ("al" "al" "alx" "alex" "al") (0 3 2 1 4)))