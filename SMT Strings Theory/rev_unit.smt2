(set-logic UFSLIA)
(define-fun rev_of ((s String) (r String)) Bool
    (or 
    (and (forall ((i Int)) (or (>= i (str.len s)) (= (str.at s i) (str.at r (- (str.len s) (+ i 1))) ))) (= (str.len s) (str.len r)) )
    (and (= (str.len s) 0) (= (str.len r) 0 ))))
(declare-fun s1 () String)
(declare-fun sx () String)
(declare-fun r1 () String)
(declare-fun r2 () String)
(assert (= (str.len sx) 1))
(assert (rev_of (str.++ s1 sx) r1))
(assert (rev_of s1 r2))
(assert  (= r1 (str.++ sx r2) ))
(check-sat)
(get-model)
(exit)
