(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

; (declare-sort Node 0)
(declare-sort Epoch 0)
;bounded
(declare-datatypes ((Node 0)) (((Node0) (Node1) (Node2))))

;state predicates
(declare-fun transfer (Epoch Node) Bool)
(declare-fun locked (Epoch Node) Bool)
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
(declare-fun R8 () Bool)
(declare-fun P () Bool)

(declare-fun __transfer (Epoch Node) Bool)
(declare-fun __locked (Epoch Node) Bool)
(declare-fun __ep (Node) Epoch)
(declare-fun __held (Node) Bool)
(declare-fun __lt (Epoch Epoch) Bool)
(declare-fun __R () Bool)
(declare-fun __R1 () Bool)
(declare-fun __R2 () Bool)
(declare-fun __R3 () Bool)
(declare-fun __R4 () Bool)
(declare-fun __R5 () Bool)
(declare-fun __R6 () Bool)
(declare-fun __R7 () Bool)
(declare-fun __R8 () Bool)
(declare-fun __P () Bool)
(declare-fun zero () Epoch)
(declare-fun T () Bool)
(declare-fun I () Bool)

(declare-fun is_max (Node) Bool)
(declare-fun __is_max (Node) Bool)

(assert 
    (forall ((n Node))
        (=
            (is_max n)
            (forall ((m Node))
                (=>
                    (not (= m n))
                    (lt (ep m) (ep n))
                )
            )
        )
    )
)

(assert 
    (forall ((n Node))
        (=
            (__is_max n)
            (forall ((m Node))
                (=>
                    (not (= m n))
                    (lt (__ep m) (__ep n))
                )
            )
        )
    )
)

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
    )
)

(assert
    (and
        ; held mutual exlcusion
        (= 
            R1
            (forall ((n Node) (m Node))
                (=>
                    (and (held n) (held m))
                    (= n m)
                )
            )
        )
        (= 
            __R1
            (forall ((n Node) (m Node))
                (=>
                    (and (__held n) (__held m))
                    (= n m)
                )
            )
        )
        ; if holding, then there is no transfer at current time
        (= 
            R2
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (and (held n) (lt (ep n) e))
                    (not (transfer e m))
                )
            )
        )
        (= 
            __R2
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (and (__held n) (lt (__ep n) e))
                    (not (__transfer e m))
                )
            )
        )
        ;mutual exclusion on transfer
        (= 
            R3
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (and (transfer e n) (transfer e m))
                    (= n m)
                )
            )
        )
        (= 
            __R3
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (and (__transfer e n) (__transfer e m))
                    (= n m)
                )
            )
        )
        ; if locked in present, then holding, 
        (= 
            R4
            (forall ((n Node))
                (=>
                    (locked (ep n) n)
                    (held n)
                )
            )
        )
        (= 
            __R4
            (forall ((n Node))
                (=>
                    (__locked (ep n) n)
                    (__held n)
                )
            )
        )

        ; if no holder in the present, then there is a transfer message at time 
        ; larger than all local timestamps
        (= 
            R5
            (=>
                (forall ((n Node)) (not (held n)))
                (exists ((e Epoch) (m1 Node))
                    (and
                        (transfer e m1)
                        (forall ((m2 Node))
                            (lt (ep m2) e)
                        )
                    )
                )
            )
        )
        (= 
            __R5
            (=>
                (forall ((n Node)) (not (__held n)))
                (exists ((e Epoch) (m1 Node))
                    (and
                        (__transfer e m1)
                        (forall ((m2 Node))
                            (__lt (__ep m2) e)
                        )
                    )
                )
            )
        )
        ; the holding node has the largest local timestamp
        (= 
            R6
            (forall ((n Node))
                (=>
                    (held n)
                    (forall ((m Node))
                        (=>
                            (not (= m n))
                            (lt (ep m) (ep n))
                        )
                    )
                )
            )
        )
        (= 
            __R6
            (forall ((n Node))
                (=>
                    (__held n)
                    (forall ((m Node))
                        (=>
                            (not (= m n))
                            (__lt (__ep m) (__ep n))
                        )
                    )

                )
            )
        )
        ;no locks in future
        (=
            R7
            (forall ((n Node) (e Epoch))
                (=>
                    (lt (ep n) e)
                    (not (locked e n))
                )
            )
        )
        (=
            __R7
            (forall ((n Node) (e Epoch))
                (=>
                    (__lt (__ep n) e)
                    (not (__locked e n))
                )
            )
        )
        ; eps unique
        (=
            R8
            (forall ((n Node) (m Node))
                (=>
                    (= (ep n) (ep m))
                    (= m n)
                )
            )
        )
        (=
            __R8
            (forall ((n Node) (m Node))
                (=>
                    (= (__ep n) (__ep m))
                    (= m n)
                )
            )
        )
    )
)

(assert 
    (=
        R
        (and R1 R2 R3 R4 R5 R6 R7 R8)
    )
)
(assert 
    (=
        __R
        (and __R1 __R2 __R3 __R4 __R5 __R6 __R7 __R8)
    )
)

(assert 
    (forall ((e Epoch))
        (=>
            (not (= e zero))
            (lt zero e)
        )
    )
)

(assert 
    (forall ((e1 Epoch) (e2 Epoch))
        (= (lt e1 e2) (__lt e1 e2))
    )
)

(assert
    (=
        I
        (exists ((first Node) (e Epoch))
            (and
                (not (= e zero))
                (forall ((n Node) (e1 Epoch))
                    (=>
                        (not (= n first))
                        (and
                            (not (held n))
                            (= (ep n) zero)
                            (not (transfer e1 n))
                            (not (locked e1 n))
                        )
                    )
                )
                (held first)
                (= (ep first) e)
                (forall ((e1 Epoch))
                    (and
                        (not (transfer e1 first))
                        (not (locked e1 first))
                    )
                )
            )
        )
    )
)

(assert 
    (=
        T
        (or
            ; grant
            (exists ((n1 Node) (n2 Node) (e Epoch))
                (and
                    (held n1)
                    (lt (ep n1) e)
                    (__transfer e n2)
                    (not (__held n1))
                    (forall ((m1 Node) (m2 Node) (e_ Epoch))
                        (and
                            (=>
                                (not (= n1 m1))
                                (and
                                    (= (held m1) (__held m1))
                                )
                            )
                            (=> 
                                (not (= m2 n2))
                                (= (__transfer e_ m2) (transfer e_ m2))
                            )
                            (= (locked e_ m1) (__locked e_ m1))
                            (= (ep m1) (__ep m1))
                            (=>
                                (not (= e e_))
                                (= (transfer e_ n2) (__transfer e_ n2))
                            )
                        )
                    )
                )
            )
            ; accept
            (exists ((n Node) (e Epoch))
                (and
                    (transfer e n)
                    (not (__transfer e n))
                    (lt (ep n) e)
                    (__held n)
                    (= (__ep n) e)
                    (__locked e n)
                    (forall ((m Node) (e1 Epoch))
                        (and
                            (=>
                                (not (= m n))
                                (and
                                    (= (held m) (__held m))
                                    (= (ep m) (__ep m))
                                    (= (locked e1 m) (__locked e1 m))
                                    (= (transfer e1 m) (__transfer e1 m))
                                )
                            )
                            (=>
                                (not (= e e1))
                                (and
                                    (= (locked e1 n) (__locked e1 n))
                                    (= (transfer e1 n) (__transfer e1 n))
                                )
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
        P
        (forall ((n Node) (m Node) (e Epoch))
            (=> 
                (and (locked e n) (locked e m))
                (= n m)
            )
        )
    )
)
(assert
    (=
        __P
        (forall ((n Node) (m Node) (e Epoch))
            (=> 
                (and (__locked e n) (__locked e m))
                (= n m)
            )
        )
    )
)

;(assert
;(not
;   (=> __R __P)
;)
;)

(assert 
    (not 
        (=> (and R T) __R)
    )
)

;(assert (not (=> I R)))

;(assert (and I T))


(check-sat)
(get-model)