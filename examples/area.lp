

area(X,Y,A) :- A = X*Y.

query(A) :- area(4,4,A).



dist(X,Y,D) :- D = ||X-Y||.

query(X) :- dist(1,5,X).

#magic area/3.
#magic dist/3.