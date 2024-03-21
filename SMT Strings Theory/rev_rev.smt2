(set-logic SLIA)
(declare-fun s1 () String)
(declare-fun r1 () String)
(declare-fun r2 () String)
(define-fun rev_of ((s String) (r String)) Bool
    (or 
    (and (forall ((i Int)) (or (>= i (str.len s)) (= (str.at s i) (str.at r (- (str.len s) (+ i 1))) ))) (= (str.len s) (str.len r)) )
    (and (= (str.len s) 0) (= (str.len r) 0 ))))
(assert (rev_of s1 r1))
(assert (rev_of r1 r2))
(assert (= s1 r2))
(check-sat)
(get-model)
(exit)
