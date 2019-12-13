node(1..n).
feature(1..k).

% Constraint 1
not v(1).

%Constraint 2
not l(I,J) :- v(I), node(I), node(J).
v(I) :- not suml(I), node(I).

%Constraint 3
l(I,J) :- node(I), node(J), r(I,K), K = J + 1.
r(I,J) :- node(I), node(J), l(I,K), K = J - 1.

% Constraint 4
suml(I) :- not v(I), node(I).
suml(I) :- l(I,_), node(I).
1{l(I,J): node(J), J >= I + 1, J <= 2*I, J \ 2 = 0}1 :- suml(I), node(I).

% Contraint 5
l(I,J) :- node(I), node(J), p(J,I), J >= I + 1, J <= 2*I, J \ 2 = 0.
r(I,J) :- node(I), node(J), p(J,I), J >= I + 2, J <= 2*I + 1, J \ 2 = 1.
p(J,I) :- node(I), node(J), l(I,J), J >= I + 1, J <= 2*I, J \ 2 = 0.
p(J,I) :- node(I), node(J), r(I,J), J >= I + 2, J <= 2*I + 1, J \ 2 = 1.

%% Constraint 6
1{p(J,I) : I=J/2..J-1}1 :- J=2..n.

% Constraint 7
d0(R,J) :- p(J,I), d0(R,I).
d0(R,J) :- a(R,I), r(I,J).
not d0(R,1) :- R=1..k.
1{d0(R,I); a(R,I): r(I,J)}1 :- p(J,I), d0(R,J).

% Constraint 8
d1(R,J) :- p(J,I), d1(R,I).
d1(R,J) :- a(R,I), l(I,J).
not d1(R,1) :- R=1..k.
1{d1(R,I); a(R,I): l(I,J)}1 :- p(J,I), d1(R,J).

% Constraint 9
not a(R,J) :- u(R,I), p(J,I).
u(R,J) :- a(R,J).
u(R,J) :- u(R,I), p(J, I).

% Constraint 10
1{a(R,J): feature(R)}1 :- not v(J), node(J).

% Constraint 11
not a(R,J) :- v(J), R=1..k.

% Generate c's
1{c(J); not c(J)}1 :- v(J).

#show v/1.
#show c/1.
#show l/2.
#show r/2.
#show p/2.
#show a/2.