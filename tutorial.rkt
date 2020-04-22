#lang rosette/safe

(require rosette/lib/match)
(require rosette/lib/angelic)
(require rosette/lib/synthax)

;;; Demonstration of solving a constraint in Rosette.
(displayln "-------- Constraint --------")
; Compute the absolute value of `x`.
(define (absv x)
  (if (< x 0) (- x) x))

; Define a symbolic variable called y of type integer.
(define-symbolic i1 i2 i3 integer?)

; Solve a constraint saying |i1| = 5.
(displayln "Solving |i1| = 5")
(displayln (solve (assert (= (absv i1) 5))))

; Solve a constraint saying |i1| < 0.
(displayln "Solving |i1| < 0")
(displayln (solve (assert (< (absv i1) 0))))

;;; Demonstration of how to define a DSL in Rosette.
(displayln "-------- DSL ---------")
; The syntax of the DSL.
(struct plus (left right) #:transparent)
(struct mul (left right) #:transparent)
(struct square (arg) #:transparent)
; The semantics of the DSL.
(define (interpret p)
  (match p
    [(plus a b) (+ (interpret a) (interpret b))]
    [(mul a b)   (* (interpret a) (interpret b))]
    [(square a)  (expt (interpret a) 2)]
    [_ p]))

(define prog (plus (square 7) 3))
(displayln "Interpreting the program")
(displayln (interpret prog))

(displayln "Evaluating a program with symbolic values")
(displayln (interpret (square (plus i1 2))))

(displayln "Solving constraints")
(displayln (solve 
            (assert 
             (= (interpret (mul i1 i2)) (+ i2 i2)))))
(displayln 
 (synthesize
  #:forall (list i2)
  #:guarantee (assert (= (interpret (mul i1 i2)) (+ i2 i2)))))

;;; Sketch
(displayln "-------- Sketch --------")
(define (??expr . terminals)
  (define a (apply choose* terminals))
  (define b (apply choose* terminals))
  (choose* (plus a b)
           (mul a b)
           (square a)
           a))

(define sketch (plus (??expr i1 i2) (??expr i1 i2)))

(define M
  (synthesize
   #:forall (list i1 i2)
   #:guarantee (assert (= (interpret sketch) (+ i2 (* 2 i1))))))

(displayln (evaluate sketch M))

;;; SyGuS
(displayln "-------- SyGuS --------")
#|
(synth-fun f ((x Int) (y Int)) Int
  ((Start Int (x y
                 (Constant Int)
                 (+ Start Start)
                 (* Start Start)))))
(declare-var a Int)
(declare-var a Int)
(constraint (=> (>= y 0) (>= (f x y) (* x 2))))
(constraint (=> (< y 0) (< (f x y) (* x 2))))
(check-synth)
|#

#|
binary-expr x y 2 is:
OP -> plus | mul
VAR -> x | y
S -> VAR | OP VAR S'
S' -> VAR | OP VAR S''
S'' -> VAR | Int
|#
(define hole (?? integer?))
(define-synthax (binary-expr x y depth)
  #:base (choose x y hole)
  #:else (choose
          x y
          ((choose plus mul) (choose x y)
                             (binary-expr x y (- depth 1)))))

(define (constraint func x y)
  (let ([result (interpret (func x y))])
    (and (=> (>= y 0) (>= result (* x 2)))
         (=> (< y 0) (< result (* x 2))))))

(define (binary-func x y) (binary-expr x y 2))
(define M1 (synthesize
            #:forall (list i1 i2)
            #:guarantee (assert (constraint binary-func i1 i2))))
(displayln (evaluate (binary-func i1 i2) M1))

;;; PbE
(displayln "-------- PbE --------")
(struct in-out-pair (in out) #:transparent)
(define (assertion sketch examples)
  ; sketch: input function with holes
  ; examples: a list of input/output pairs
  (if (null? examples)
      (void)
      (let* ([cur (car examples)]
             [rest (cdr examples)])
        (match cur
          [(in-out-pair in out)
           (assert (= (interpret (apply sketch in)) out))
           (assertion sketch rest)]))))
(define examples (list (in-out-pair (list 2 3) 7)
                       (in-out-pair (list 4 -1) 7)))
(define M2 (synthesize #:forall (list)
                       #:guarantee (assertion binary-func examples)))
(displayln (evaluate (binary-func i1 i2) M2))


;;; CEGIS
(displayln "-------- CEGIS --------")
(define (oracle x y)
  (+ y (* 2 x)))

(define (CEGIS sketch arglist oracle)
  (define (iter model generated-in-out)
    (let* ([concrete-application
            (interpret (evaluate (apply sketch arglist) model))]
           [verify-model
            (verify (assert (= concrete-application
                               (apply oracle arglist))))])
      (if (unsat? verify-model)
          model
          (let* ([new-in
                  (evaluate arglist (complete-solution verify-model arglist))]
                 [new-out (apply oracle new-in)]
                 [new-generated-in-out
                  (cons (in-out-pair new-in new-out) generated-in-out)]
                 [new-model (solve (assertion sketch new-generated-in-out))])
            (if (unsat? new-model)
                (unsat)
                (iter new-model new-generated-in-out))))))
  (iter (sat) '()))

(define cegis-model (CEGIS binary-func (list i1 i2) oracle))

(displayln (evaluate (binary-func i1 i2) cegis-model))

