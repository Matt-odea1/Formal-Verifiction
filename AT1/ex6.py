def TailSize(a):
    i, size = len(a) -1, 0
    while (i >= 0 and a[i] == 0):
        if a[i] != 0:
            break
        size+=1
        i-=1
    return size

assert TailSize([1,2,0,4,0,0]) == 2
assert TailSize([1,2,0,4,0]) == 1
assert TailSize([1,2,0,4]) == 0
assert TailSize([1,2,0,4, 0,0 ,0,0 ]) == 4