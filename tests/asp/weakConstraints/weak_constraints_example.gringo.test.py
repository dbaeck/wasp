input = """
1 2 0 0
1 3 0 0
1 4 0 0
1 5 0 0
8 2 6 7 0 0
8 2 8 9 0 0
8 2 10 11 0 0
8 2 12 13 0 0
1 14 2 0 7 9
1 15 2 1 9 7
1 16 2 1 7 9
1 17 2 2 7 9
1 18 1 0 14
1 18 1 0 15
1 18 1 0 16
1 18 1 0 17
6 0 1 0 18 2
1 19 2 0 11 13
1 20 2 1 13 11
1 21 2 1 11 13
1 22 2 2 11 13
1 23 1 0 19
1 23 1 0 20
1 23 1 0 21
1 23 1 0 22
6 0 1 0 23 2
0
2 c(1)
3 c(2)
4 c(3)
5 c(4)
6 not_a(1)
8 not_a(2)
10 not_a(3)
12 not_a(4)
7 a(1)
9 a(2)
11 a(3)
13 a(4)
0
B+
0
B-
1
0
1
"""
output = """
COST 2@2 2@1
"""