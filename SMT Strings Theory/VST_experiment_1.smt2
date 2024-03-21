(set-logic UFSLIA)
(define-fun sublist ((n Int) (m Int) (s String)) String
	(ite (< n 0) (str.substr s 0 m) 
	(ite (< m 0) (str.substr s n 0)
		(str.substr s n (- m n))
	)))
(declare-fun a () String)
(assert (= 1 (str.len a)))
(declare-fun xs () String)
(assert (not (= (sublist 0 (str.len (str.++ a xs)) (str.++ a xs) ) (str.++ a xs) )))
(check-sat)
(exit)