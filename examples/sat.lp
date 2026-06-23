atom(p;q;r).
formula(f1, and(neg(p),or(q,neg(r)) ) ).
%formula(f2, or(neg(p), q)).

{true(X):atom(X)}.

:- formula(f1,F), not sat(F).

#show true/1.

#magic sat/1.
sat(P) :- true(P).
sat(and(A,B)) :- sat(A), sat(B).
sat(or(A,_)) :- sat(A).  
sat(or(_,B)) :- sat(B).
sat(neg(A)) :- not sat(A).


