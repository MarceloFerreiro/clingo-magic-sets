edge(1,2).
edge(2,3).
edge(2,4).
edge(3,5).

edge(6, 7).
edge(7,8).

source(1).



#magic reach/2.
reach(X, Y) :- edge(X, Y).
reach(X, Z) :- reach(X, Y), edge(Y, Z).
reachable(Y) :- source(X), reach(X, Y).

query(X) :- reach(X, Y), source(X).