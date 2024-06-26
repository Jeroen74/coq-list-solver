(set-logic UFSLIA)
(define-fun sublist ((n Int) (m Int) (s String)) String
	(ite (< n 0) (str.substr s 0 m) 
	(ite (< m 0) (str.substr s n 0)
		(str.substr s n (- m n))
	)))
(declare-fun a () String)
(assert (= 1 (str.len a)))
(declare-fun xs () String)
(assert (not (= (sublist 1 (str.len (str.++ a xs)) (str.++ a xs) ) xs )))
(check-sat)
(exit)