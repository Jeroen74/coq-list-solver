(set-logic UFSLIA)
(define-fun sublist ((n Int) (m Int) (s String)) String
	(ite (< n 0) (str.substr s 0 m) 
	(ite (< m 0) (str.substr s n 0)
		(str.substr s n (- m n))
	)))
(define-fun min ((i Int) (j Int)) Int
	(ite (< i j) i j))
(define-fun max ((i Int) (j Int)) Int
	(ite (< i j) j i))
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun p () Int)
(declare-fun l () String)
(declare-fun temp () String)
(assert (not (= (sublist n m (str.++ (sublist 0 p l) (sublist p (str.len l) l))) (str.++ (sublist n (min m p) l) (sublist (max n p) m l)))))
(check-sat)
(exit)