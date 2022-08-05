# 15puzzle
A simple 15-puzzle solver in C++, using 6+6+3 static additive pattern database and IDA*. 

Gengerate the database in RAM when launch. You should have at least 128MB RAM for the program.

On my AMD Ryzen 7 5800H 3.2GHz, GCC 12.1 -O3 -march=native -mtune=native

Gengerat database costs 1.3s 

For the 17 hardest 80-step puzzles, average time = 7.1s

For 10000 random puzzle, average time = 4.232ms (get random permutaion untill 10000 legal puzzles)

(Using no pragma besides -O2 cost 4% more time)
 
The multi-thread version code might be implemented later.
