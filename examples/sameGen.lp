% Same Generation — ejemplo clásico de magic sets (Bancilhon et al. 1986)
%
% sg(X, Y): X e Y son de la misma generación en un árbol genealógico.
%
% EDB:
%   flat(X, Y)  — X e Y son hermanos (misma generación directamente)
%   up(X, P)    — P es padre de X
%   down(P, X)  — X es hijo de P (inverso de up)

% Árbol:          p ---flat--- q
%               / \             \
%              a   b             c

up(a, p).  up(b, p).  up(c, q).
down(p, a). down(p, b). down(q, c).
flat(p, q). flat(q, p).

% Query: ¿son X e Y de la misma generación?
% startPair da los dos argumentos ligados → adornamiento bb en sg.
startPair(a, c).

% Reglas MDB
#magic sg/2.
sg(X, Y) :- flat(X, Y).
sg(X, Y) :- up(X, X1), sg(X1, Y1), down(Y1, Y).

query(X, Y) :- startPair(X, Y), sg(X, Y).
#show query/2.
