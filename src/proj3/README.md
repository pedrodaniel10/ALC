# ALC - 2019/2020 - Project 3
Algorithms for Computational Logic's project.

## Introduction
The program outputs the smallest decision tree that classifies the given samples. It runs first the ID3 algorithm [[Qui86](http://www.hunch.net/~coms-4771/quinlan.pdf)] to retrieve a small valid tree using heuristics. The ID3 doesn't guarantee to return the smallest tree, so the program uses it as an upper bound. From that point, it calls multiple times Minizinc in descendent order of the number of nodes (only with odd numbers) until finds an _UNSAT_ encoding. In the best case, ID3 returns the smallest tree with **N** nodes and there is only one Minizinc call to check the existence of a tree with **N-2** nodes that returns _UNSAT_.

**_DISCLAIMER:_** The ID3 algorithm's implementation was not made by me! It was downloaded from https://github.com/tofti/python-id3-trees and adapted by me to this problem

All the problem encoding is in the file **main.mzn**, the only 2 constraints not there are the assigment of the samples that are made in **proj3.py**.
The encoding is a straightforward implementation from [[Narodytska et al](https://www.ijcai.org/proceedings/2018/0189.pdf)]. There were just a few optimizations, mainly in the following constraints:
- **Constraint 1:** I also explicitly say that the nodes numbered N-1 and N are leaves. Meaning that I add 2 constraints saying that v<sub>N-1</sub> and v<sub>N</sub> are **true**.
- **Constraint 2 and 11:** I skip the iteration where i=1, as v<sub>1</sub> is the root and non-leaf.
- **Constraint 4, 5 and 10:** I skip the iterations where i=N-1 and i=N, as those nodes are already leaves.
- **Constraint 12 and 13:** I skip the iteration where j=1, as the node 1 is the root and non-leaf.
- Added additional constraints λ and τ: improved performance by a factor of 10 in some cases.

Other notes:
- For the calculation of LR(i) and RR(i) I added one more constraint beyond parity that is that the difference between i and the element of those sets be greater or equal than 1 and 2 respectively to avoid wrong possible children.
- Also, wrong children, meaning that doesn't belong to LR(i) or RR(i) are set to false (added as constraint). 

## Requirements
- GNU/Linux
- Python 3
- Minizinc

For backend solvers, by default is **Chuffed** as it was the fastest during testing. It can also use **Geocode** or **CPLEX** as backend solver, just need to change line 15 to one of these:
```python
solver = solvers["Geocode"]
solver = solvers["CPLEX"]
```
**_NOTE:_** For CPLEX you also might need to change the path to the library in line 11. This may occur if you use different version of CPLEX (12.9 is the expected) or CPLEX was installed in another path than the default.

## How to run
The project can be executed is different ways, if you are in the same folder:

```bash
    python3 ./proj3.py 
```
Or like:
```bash
    ./proj3
```

The program expects input for stdin, so you can feed him with an example file:
```bash
    ./proj3 < example.smp
```

## References
[[Narodytska et al](https://www.ijcai.org/proceedings/2018/0189.pdf)] N. Narodytska, A. Ignatiev, F. Pereira, and J. Marques-Silva.  Learning optimal decision trees with SAT.  In J. Lang, editor,Proceedings of the Twenty-Seventh International JointConference on Artificial Intelligence, IJCAI 2018, July 13-19, 2018, Stockholm, Sweden.,pages 1362–1368. ijcai.org, 2018.

[[Qui86](http://www.hunch.net/~coms-4771/quinlan.pdf)] J. R. Quinlan,Induction of decision trees, Mach. Learn.1(1986), no. 1, 81–106.