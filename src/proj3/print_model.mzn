%run solver
solve satisfy;

% example prints
output [ "l \(i) \(j)\n" | i in NODES, j in NODES where fix(l[i,j])] ;
output [ "r \(i) \(j)\n" | i in NODES, j in NODES where fix(r[i,j])] ;
output [ "a \(r) \(j)\n" | r in FEATURES, j in NODES where fix(a[r,j])] ;

array[NODES] of var int: cl;
constraint forall(i in NODES) (cl[i] = if c[i] then 1 else 0 endif);

output [ "c \(i) \(cl[i])\n" | i in NODES where fix(v[i])] ;
