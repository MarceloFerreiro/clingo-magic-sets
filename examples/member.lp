% Lista  cons(H,T) / nil.
% Como en Prolog: member(X, [1,2,3]).

lista(cons(1, cons(2, cons(3, nil)))).

% estas dos reglas son problemáticas:
%   - La base member(X, cons(X,_)). es unsafe.
%   - La recursiva tiene grounding infinito.

#magic member/2.

member(X, cons(X, _)).
member(X, cons(_, T)) :- member(X, T).

query(X) :- lista(L), member(X, L).

#show query/1.
