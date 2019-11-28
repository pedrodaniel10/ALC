# ALC - 2019/2020 - Project 1
Algorithms for Computational Logic's project.

## Introduction
The work is a straightforward implementation from the paper [Narodytska et al, IJCAI 18](https://www.ijcai.org/proceedings/2018/0189.pdf). There were just a few optimizations, mainly in the following constraints:
- **Constraint 1:** I also explicitly say that the nodes numbered N-1 and N are leaves. Meaning that I add 2 constraints saying that v<sub>N-1</sub> and v<sub>N</sub> are **true**.
- **Constraint 2 and 11:** I skip the iteration where i=1, as v<sub>1</sub> is the root and non-leaf.
- **Constraint 4, 5 and 10:** I skip the iterations where i=N-1 and i=N, as those nodes are already leaves.
- **Constraint 12 and 13:** I skip the iteration where j=1, as the node 1 is the root and non-leaf.

Other notes:
- For the cardinality constraint for k<=(x1, ..., xn) where k=1, I implemented [Sinz, 2015](http://www.carstensinz.de/papers/CP-2005.pdf).
- For the calculation of LR(i) and RR(i) I added one more constraint beyond parity that is that the difference between i and the element of those sets be greater or equal than 1 and 2 respectively to avoid wrong possible children.
- Also, wrong children, meaning that doesn't belong to LR(i) or RR(i) are set to false (added as constraint). 

## Requirements
- GNU/Linux
- Python 3
- Lingeling (there is a x86-64 ELF executable in **src/**)

## How to run
The program assumes that the SAT solver (lingeling) is in the same directory where the program runs. So, in order to run without problems:

```bash
    cd src/
```

And you can run in various ways like:

```bash
    python3 ./proj1.py 
```
Or like:
```bash
    ./proj1
```

The program expects input for stdin, so you can feed him with an example file:
```bash
    ./proj1 < example.smp
```

## References
[[Narodytska et al](https://www.ijcai.org/proceedings/2018/0189.pdf)] N. Narodytska, A. Ignatiev, F. Pereira, and J. Marques-Silva.  Learning optimal decision trees with SAT.  In J. Lang, editor,Proceedings of the Twenty-Seventh International JointConference on Artificial Intelligence, IJCAI 2018, July 13-19, 2018, Stockholm, Sweden.,pages 1362–1368. ijcai.org, 2018.