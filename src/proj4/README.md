# ALC - 2019/2020 - Project 4 
Algorithms for Computational Logic's project.

## Introduction
The program outputs the smallest decision tree that classifies the given samples. It runs first the ID3 algorithm [[Qui86](http://www.hunch.net/~coms-4771/quinlan.pdf)] to retrieve a small valid tree using heuristics. The ID3 doesn't guarantee to return the smallest tree, so the program uses it as an upper bound. From that point, it calls multiple times clingo in descendent order of the number of nodes (only with odd numbers) until finds an _UNSAT_ encoding. In the best case, ID3 returns the smallest tree with **N** nodes and there is only one clingo call to check the existence of a tree with **N-2** nodes that returns _UNSAT_.

**_DISCLAIMER:_** The ID3 algorithm's implementation was not made by me! It was downloaded from https://github.com/tofti/python-id3-trees and adapted by me to this problem

Almost all the problem encoding is in the file **main.lp**, the only  constraints not there are the assignment of the samples (Constraints 12 and 13) that are made in **proj4.py**.
The encoding is a straightforward implementation from [[Narodytska et al](https://www.ijcai.org/proceedings/2018/0189.pdf)]. There were just a few optimizations, mainly in the following constraints:
- Added additional constraints λ and τ: improved performance by a factor of 10 in some cases.

## Requirements
- GNU/Linux
- Python 3
- clingo

## How to run
The project can be executed is different ways, if you are in the same folder:

```bash
    python3 ./proj4.py 
```
Or like:
```bash
    ./proj4
```

The program expects input for stdin, so you can feed him with an example file:
```bash
    ./proj4 < example.smp
```

## References
[[Narodytska et al](https://www.ijcai.org/proceedings/2018/0189.pdf)] N. Narodytska, A. Ignatiev, F. Pereira, and J. Marques-Silva.  Learning optimal decision trees with SAT.  In J. Lang, editor,Proceedings of the Twenty-Seventh International JointConference on Artificial Intelligence, IJCAI 2018, July 13-19, 2018, Stockholm, Sweden.,pages 1362–1368. ijcai.org, 2018.

[[Qui86](http://www.hunch.net/~coms-4771/quinlan.pdf)] J. R. Quinlan,Induction of decision trees, Mach. Learn.1(1986), no. 1, 81–106.