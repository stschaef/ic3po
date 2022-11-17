(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

; (declare-sort Node 0)
(declare-sort Epoch 0)
;bounded
(declare-datatypes ((Node 0)) (((node0) (node1) (node2))))

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
(declare-fun __P () Bool)
(declare-fun zero () Epoch)
(declare-fun T () Bool)
(declare-fun I () Bool)

(declare-fun concrete_R () Bool)
(declare-fun __concrete_R () Bool)

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

; (assert
;     ;at least two epochs
;     (exists ((e1 Epoch) (e2 Epoch))
;         (and
;             (not (= e1 e2))
;         )
;     )
; )

; (assert
;     (forall ((N Node) (e Epoch))
;         (or 
;             (lt (ep N) e)
;             (= (ep N) e)
;         )
;     )
; )

(assert
    (and
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
            __R2
            (forall ((n Node) (m Node) (e Epoch))
                (=>
                    (__held n)
                    (not (__transfer e m))
                )
            )
        )
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
        (= 
            R4
            (forall ((n Node) (e Epoch))
                (=>
                    (locked e n)
                    (held n)
                )
            )
        )
        (= 
            __R4
            (forall ((n Node) (e Epoch))
                (=>
                    (__locked e n)
                    (__held n)
                )
            )
        )
        (= 
            R5
            (forall ((e Epoch))
                (exists ((n Node))
                    (or 
                        (held n)
                        (transfer e n)
                    )
                )
            )
        )
        (= 
            __R5
            (forall ((e Epoch))
                (exists ((n Node))
                    (or 
                        (__held n)
                        (__transfer e n)
                    )
                )
            )
        )
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
        (= 
            R7
            (forall ((n Node) (e Epoch))
                (=>
                    (transfer e n)
                    (lt (ep n) e)
                )
            ) 
        )
        (= 
            __R7
            (forall ((n Node) (e Epoch))
                (=>
                    (__transfer e n)
                    (__lt (__ep n) e)
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
        __R
        (and __R1 __R2 __R3 __R4 __R5 __R6 __R7)
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
                    (not (held n1))
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
        concrete_R
        (and
            (exists ((e Epoch))
                (and
                    (forall ((n Node))
                        (not (lt e (ep n)))
                    )
                    (exists ((m Node))
                        (= e (ep m))
                    )
                    (or
                        ; init
                        (and
                            (held node0) (not (held node1)) (not (held node2))
                            (not (locked e node0)) (not (locked e node1)) (not (locked e node2))
                            (not (transfer e node0)) (not (transfer e node1)) (not (transfer e node2))
                        )
                        (and
                            (not (held node0)) (held node1) (not (held node2))
                            (not (locked e node0)) (not (locked e node1)) (not (locked e node2))
                            (not (transfer e node0)) (not (transfer e node1)) (not (transfer e node2))
                        )
                        (and
                            (not (held node0)) (not (held node1)) (held node2)
                            (not (locked e node0)) (not (locked e node1)) (not (locked e node2))
                            (not (transfer e node0)) (not (transfer e node1)) (not (transfer e node2))
                        )
                        ; transfer
                        (and
                            (not (held node0)) (not (held node1)) (not (held node2))
                            (not (locked e node0)) (not (locked e node1)) (not (locked e node2))
                            (transfer e node0) (not (transfer e node1)) (not (transfer e node2))
                        )
                        (and
                            (not (held node0)) (not (held node1)) (not (held node2))
                            (not (locked e node0)) (not (locked e node1)) (not (locked e node2))
                            (not (transfer e node0)) (transfer e node1) (not (transfer e node2))
                        )
                        (and
                            (not (held node0)) (not (held node1)) (not (held node2))
                            (not (locked e node0)) (not (locked e node1)) (not (locked e node2))
                            (not (transfer e node0)) (not (transfer e node1)) (transfer e node2)
                        )
                        ; locked
                        (and
                            (held node0) (not (held node1)) (not (held node2))
                            (locked e node0) (not (locked e node1)) (not (locked e node2))
                            (not (transfer e node0)) (not (transfer e node1)) (not (transfer e node2))
                        )
                        (and
                            (not (held node0)) (held node1) (not (held node2))
                            (not (locked e node0)) (locked e node1) (not (locked e node2))
                            (not (transfer e node0)) (not (transfer e node1)) (not (transfer e node2))
                        )
                        (and
                            (not (held node0)) (not (held node1)) (held node2)
                            (not (locked e node0)) (not (locked e node1)) (locked e node2)
                            (not (transfer e node0)) (not (transfer e node1)) (not (transfer e node2))
                        )
                    )
                )
            )
        )
    )
)
(assert 
    (=
        __concrete_R
        (and
            (forall ((e Epoch))
                (and
                    (or
                        ; init
                        (and
                            (__held node0) (not (__held node1)) (not (__held node2))
                            (not (__locked e node0)) (not (__locked e node1)) (not (__locked e node2))
                            (not (__transfer e node0)) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                        (and
                            (not (__held node0)) (__held node1) (not (__held node2))
                            (not (__locked e node0)) (not (__locked e node1)) (not (__locked e node2))
                            (not (__transfer e node0)) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                        (and
                            (not (__held node0)) (not (__held node1)) (__held node2)
                            (not (__locked e node0)) (not (__locked e node1)) (not (__locked e node2))
                            (not (__transfer e node0)) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                        ; __transfer
                        (and
                            (not (__held node0)) (not (__held node1)) (not (__held node2))
                            (not (__locked e node0)) (not (__locked e node1)) (not (__locked e node2))
                            (__transfer e node0) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                        (and
                            (not (__held node0)) (not (__held node1)) (not (__held node2))
                            (not (__locked e node0)) (not (__locked e node1)) (not (__locked e node2))
                            (not (__transfer e node0)) (__transfer e node1) (not (__transfer e node2))
                        )
                        (and
                            (not (__held node0)) (not (__held node1)) (not (__held node2))
                            (not (__locked e node0)) (not (__locked e node1)) (not (__locked e node2))
                            (not (__transfer e node0)) (not (__transfer e node1)) (__transfer e node2)
                        )
                        ; __locked
                        (and
                            (__held node0) (not (__held node1)) (not (__held node2))
                            (__locked e node0) (not (__locked e node1)) (not (__locked e node2))
                            (not (__transfer e node0)) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                        (and
                            (not (__held node0)) (__held node1) (not (__held node2))
                            (not (__locked e node0)) (__locked e node1) (not (__locked e node2))
                            (not (__transfer e node0)) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                        (and
                            (not (__held node0)) (not (__held node1)) (__held node2)
                            (not (__locked e node0)) (not (__locked e node1)) (__locked e node2)
                            (not (__transfer e node0)) (not (__transfer e node1)) (not (__transfer e node2))
                        )
                    )
                )
            )
        )
    )
)

; (assert
; (not
;    (=> R P)
; )
; )

; (assert 
;     (not 
;         (=> (and R T) __R)
;     )
; )

(assert (and I T))



(check-sat)
(get-model)