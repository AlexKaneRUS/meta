#lang racket

(require racket/trace)

(provide interpret)
(provide tm-interpreter)
(provide interpret-expr)

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

(define (tm-interpreter) '((read instructions tape-pos)
                           (pre-main (index := 0)
                                     (instr-ind := 0)
                                     (tape-pos := if (= (length tape-pos) 0) (cons -1 ()) tape-pos)
                                     (tape-neg := ())
                                     (goto main))
                           (main (if (equal? (length instructions) instr-ind) goto end goto main1))
                           (main1 (next-instr := list-ref instructions instr-ind)
                                  (instr-ind := + instr-ind 1)
                                  (goto interpret-left))
                           (interpret-left (if (equal? (car next-instr) 'left) goto left goto interpret-right))
                           (interpret-right (if (equal? (car next-instr) 'right) goto right goto interpret-write))
                           (interpret-write (if (equal? (car next-instr) 'write) goto write goto interpret-goto))
                           (interpret-goto (if (equal? (car next-instr) 'goto) goto goto goto interpret-if-goto))
                           (interpret-if-goto (if (equal? (car next-instr) 'if) goto if-goto goto error))
                           (goto (instr-ind := car (cdr next-instr))
                                 (goto main))
                           (if-goto (cur-val := if (>= index 0) (list-ref tape-pos (- (- (length tape-pos) 1) index)) (list-ref tape-neg (- (- (length tape-neg) 1) (- -1 index))))
                                    (instr-ind := if (equal? (car (cdr next-instr)) cur-val) (list-ref next-instr 3) instr-ind)
                                    (goto main))
                           (left (index := - index 1)
                                 (tape-neg := if (equal? (length tape-neg) (- -1 index)) (cons -1 tape-neg) tape-neg)
                                 (goto main))
                           (right (index := + index 1)
                                  (tape-pos := if (equal? (length tape-pos) index) (cons -1 tape-pos) tape-pos)
                                  (goto main))
                           (write (tape-pos := if (>= index 0) (list-set tape-pos (- (- (length tape-pos) 1) index) (car (cdr next-instr))) tape-pos)
                                  (tape-neg := if (< index 0) (list-set tape-neg (- (- (length tape-neg) 1) (- -1 index)) (car (cdr next-instr))) tape-neg)
                                  (goto main))
                           (error (return "Unknown command"))
                           (end (cur-val := if (>= index 0) (list-ref tape-pos (- (- (length tape-pos) 1) index)) (list-ref tape-neg (- (- (length tape-neg) 1) (- -1 index))))
                                (return cur-val))
                          ))

(define (tm-example) '(((left)
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
                       (write 0)) (0)))

; example of running FlowChar: (interpret (find-name) '(alex (al al alx alex al) (0 3 2 1 4)))
; example of running Turing Machine: (interpret (tm-interpreter) (tm-example))
; (interpret (find-name) '("alex" ("al" "al" "alx" "alex" "al") (0 3 2 1 4)))