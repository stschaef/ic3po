(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

;(declare-sort Node 0)
(declare-sort Epoch 0)
;bounded
(declare-datatypes ((Node 0)) (((node0) (node1))))

;state predicates
(declare-fun transfer (Epoch Node) Bool)
;(declare-fun transferE (Node) Bool)
(declare-fun locked (Epoch Node) Bool)
;(declare-fun lockedE (Node) Bool)
(declare-fun ep (Node) Epoch)
(declare-fun held (Node) Bool)
(declare-fun lt (Epoch Epoch) Bool)
(declare-fun R () Bool)
(declare-fun R1 () Bool)
(declare-fun R2 () Bool)
(declare-fun R3 () Bool)
(declare-fun R4 () Bool)
(declare-fun R5 () Bool)
(declare-fun R6 () Bool)
(declare-fun R7 () Bool)
(declare-fun P () Bool)
(declare-fun concrete_R () Bool)
;(declare-fun E () Epoch)

(assert
    (and
        ;transitivity of lt
        (forall ((e1 Epoch) (e2 Epoch) (e3 Epoch))
            (=>
                (and
                    (lt e1 e2)
                    (lt e2 e3)
                )
                (lt e1 e3)
            )   
                
        )
        ;irreflexivity of lt
        (forall ((e Epoch))
            (not (lt e e))
        )
        ;lt is connected
        (forall ((e1 Epoch) (e2 Epoch))
            (=>
                (not (= e1 e2))
                (or
                    (lt e1 e2)
                    (lt e2 e1)
                )
            )
        )

        ;antisymmetry of lt
        ;(forall ((e1 Epoch) (e2 Epoch))
        ;    (=>
        ;        (and
        ;            (lt e1 e2)
        ;            (lt e2 e1)
        ;        )
        ;        (= e1 e2)
        ;    )
        ;)
        ;;lt is total
        ;(forall ((e1 Epoch) (e2 Epoch))
        ;    (or
        ;        (lt e1 e2)
        ;        (lt e2 e1)
        ;        (= e1 e2)
        ;    )
        ;)
    )
)

(assert
    ;at least two epochs
    (exists ((e1 Epoch) (e2 Epoch))
        (and
            (not (= e1 e2))
        )
    )
)

(assert
    (forall ((N Node) (e Epoch))
        (or 
            (lt (ep N) e)
            (= (ep N) e)
        )
    )
)

(assert
    (and
        (= 
            R1
            (forall ((n Node) (e Epoch))
                (=>
                    (locked e n)
                    (held n)
                )
            )
        )
        (= 
            R2
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (held n)
                    (not (transfer e m))
                )
            )
        )
        (= 
            R3
            (forall ((n Node) (e Epoch))
                (=>
                    (held n)
                    (= (ep n) e)
                )
            )
        )
        (= 
            R4
            (forall ((n Node) (e Epoch))
                (=>
                    (not (held n))
                    (lt (ep n) e)
                )
            )
        )
        (= 
            R5
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (and
                        (held n)
                        (= (ep m) e)
                    )
                    (= n m)
                )
            )
        )
        (= 
            R6
            (exists ((n Node))
                (forall ((e Epoch))
                    (not (transfer e n))
                )
            ) 
        )
        (= 
            R7
            (forall ((n Node) (m Node))
                (=>
                    (not (= n m))
                    (or
                        (held n)
                        (exists ((s Node) (e Epoch))
                            (or
                            (= (ep m) e)
                            (transfer e s)
                            )
                        )
                    )
                )
            ) 
        )
    )
)

(assert 
    (=
        R
        (and R1 R2 R3 R4 R5 R6 R7)
    )
)

(assert
    (=
        P
        (forall ((n Node) (m Node) (e Epoch))
            (=> 
                (and (locked e n) (locked e m))
                (= n m)
            )
        )
    )
)

;(assert
;(not
;    (=> R P)
;)
;)

(assert R)

;(assert
;    (not (=> concrete_R R))
;)

(check-sat)
(get-model)