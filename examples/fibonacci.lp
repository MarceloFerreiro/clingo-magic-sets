#magic fibonacci/2.

fibonacci(0, 0).
fibonacci(1, 1).
fibonacci(N, F) :- N > 1, N1 = N-1, N2 = N-2,
                   fibonacci(N1, F1), fibonacci(N2, F2),
                   F = F1+F2.

result(X) :- fibonacci(10, X).
#show result/1.
