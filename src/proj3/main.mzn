% fixed sets
set of int: NODES=1..n;
set of int: FEATURES=1..k;

% Function LR and RR
function array[int] of var opt int: lr(int: i) =
  let {var int: lb = i+1;
       var int: ub = min(2*i, n-1);
       } in
  [x | x in lb..ub where abs(i-x) >= 1 /\ x mod 2 = 0];
  
function array[int] of var opt int: rr(int: i) =
  let {var int: lb = i+2;
       var int: ub = min(2*i + 1, n);
       } in
  [x | x in lb..ub where abs(i-x) >= 2 /\ x mod 2 != 0];

function var int: b2i(bool: b) =
  if b then 1 else 0 endif;

% example declarations of arrays if variables
array[NODES] of var bool: v;
array[NODES,NODES] of var bool: l;
array[NODES,NODES] of var bool: r;
array[NODES,NODES] of var bool: p;
array[0..n,NODES] of var bool: lamb;
array[0..n,NODES] of var bool: tau;
array[NODES] of var FEATURES: s;

% Constraint 1: ~v1
constraint not v[1];

% vn and vn-1 are leave
constraint v[n-1];
constraint v[n];

% Constraint 2: vi -> ~lij
constraint forall(i in NODES, j in fix(lr(i))) (v[i] -> not l[i,j]);

% Constraint 3: lij <-> rij+1
constraint forall(i in NODES, j in fix(lr(i))) (l[i,j] <-> r[i,j+1]);

% Constraint 4: ~vi -> sum_{j in LR(i)} lij = 1
constraint forall(i in NODES) (
  not v[i] -> sum (j in fix(lr(i))) (l[i,j]) = 1
);

% Constraint 5: pji <-> lij, pji <-> rij
constraint forall(i in NODES, j in fix(lr(i))) (p[j,i] <-> l[i,j]);
constraint forall(i in NODES, j in fix(rr(i))) (p[j,i] <-> r[i,j]);

% Constraint 6: sum_{j/2}^{min(j-1, N)} = 1
constraint forall(j in 2..n) (
  sum(i in floor(j div 2)..min(j-1, n)) (p[j,i]) = 1
);

% Additional Constraints:
% lamb_0_i = 1 for 1 <= i <= n
constraint forall(i in NODES) (lamb[0, i]);
% lamb_t_i <-> (lamb_t_i-1 || lamb_t-1_i-1 && vi)
constraint forall(i in NODES, t in 1..floor(i div 2)) (
  lamb[t,i] <-> (lamb[t, i-1] \/ lamb[t-1,i-1] /\ v[i])
);
% Proposition 2: 
constraint forall(i in NODES, t in 0..floor(i div 2)) (
  lamb[t,i] -> not l[i, 2*(i-t+1)] /\ not r[i, 2*(i-t+1)+1]
);

% Additional Constraints:
% tau_0_i = 1 for 1 <= i <= n
constraint forall(i in NODES) (tau[0, i]);
% tau_t_i <-> (tau_t_i-1 || tau_t-1_i-1 && ~vi)
constraint forall(i in NODES, t in 1..i) (
  tau[t,i] <-> (tau[t, i-1] \/ tau[t-1,i-1] /\ not v[i])
);
% Proposition 3: 
constraint forall(i in NODES, t in ceil(i div 2)..i) (
  tau[t,i] -> not l[i, 2*(t-1)] /\ not r[i, 2*t-1]
);