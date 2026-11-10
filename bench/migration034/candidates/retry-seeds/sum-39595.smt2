(set-option :random-seed 39595)
(define-fun-rec sum ((n Int)) Int (ite (<= n 0) 0 (+ n (sum (- n 1)))))
(declare-const k Int)(assert (and (>= k 0) (= (sum k) 6)))(check-sat)(get-model)(get-value (k))
