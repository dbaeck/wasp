input = """
1 2 0 0
1 3 0 0
1 4 0 0
1 5 0 0
1 6 2 1 7 8
1 7 2 1 6 8
1 8 0 0
1 9 2 1 10 11
1 10 2 1 9 11
1 11 0 0
2 12 2 0 2 9 6
1 1 1 0 12
0
7 nall(a,2)
10 nall(a,1)
5 cap(1)
3 b(1)
4 b(2)
6 all(a,2)
9 all(a,1)
2 a(a)
0
B+
0
B-
1
0
1
"""
output = """
{a(a), b(1), b(2), cap(1), all(a,2), nall(a,1)}
{a(a), b(1), b(2), cap(1), nall(a,2), all(a,1)}
{a(a), b(1), b(2), cap(1), nall(a,2), nall(a,1)}
"""
