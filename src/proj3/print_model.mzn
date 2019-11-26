%run solver
solve satisfy;

% example prints
output [ "# v \(i) = \(v[i])\n" | i in NODES ] ;
output [ "# l \(i) \(j) = \(l[i,j])\n" | i in NODES, j in NODES where fix(l[i,j])] ;
output [ "# r \(i) \(j) = \(r[i,j])\n" | i in NODES, j in NODES where fix(r[i,j])] ;
output [ "# p \(j) \(i) = \(p[j,i])\n" | j in NODES, i in NODES where fix(p[j,i])] ;
output [ "# a \(r) \(j) = \(a[r,j])\n" | r in NODES, j in NODES where fix(a[r,j])] ;
output [ "# c \(i) = \(c[i])\n" | i in NODES ] ;
%output [ "y \(i) = \(y[i])\n" | i in NODES ] ;
%output [ "s \(i) = \(s[i])\n" | i in NODES ] ;

% watch out for the 'fix' application
%output [ "true xs:" ] ++ [ " \(i)" | i in NODES where fix(x[i]) ] ++ ["\n"];
