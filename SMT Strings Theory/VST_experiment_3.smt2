(set-logic UFSLIA)
(define-fun sublist ((n Int) (m Int) (s String)) String
	(ite (< n 0) (str.substr s 0 m) 
	(ite (< m 0) (str.substr s n 0)
		(str.substr s n (- m n))
	)))
(declare-fun j () Int)
(declare-fun size () Int)
(declare-fun l () String)
(assert (= (str.len l) size))
(assert (<= 0 j))
(assert (<= (- (- size j) 1) j))
(assert (<= j (- size j)))
(assert (not (= 
				(str.++ 
					(str.++ 
						(sublist (- (str.len l) (str.len l)) (- (str.len l) (- size j)) l) 
						(sublist j (- size j) l)) 
					(sublist (- (str.len l) j) (- (str.len l) 0) l)) 
				l)))
(check-sat)
(exit)