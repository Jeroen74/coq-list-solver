(set-logic UFSLIA)
(declare-fun l1 () String)
(declare-fun l2 () String)
(declare-fun l3 () String)
(assert (= (str.++ l1 l2) (str.++ l1 l3)))
(assert (not (= l2 l3)))
(check-sat)
(exit)