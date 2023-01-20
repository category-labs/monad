from siblings import are_siblings
from nodes import Leaf, Branch

def is_first_in_branch(i, nodes):
    if i == 0:
        return False

    return isinstance(nodes[i-1], Branch)

def peek_left(i, nodes):
    if i == 0:
        return None

    if is_first_in_branch(i, nodes):
        return peek_left(i-1, nodes)

    for index in range(i-1, 0, -1):
        if are_siblings(index, i, nodes):
            return index

def find_parent(i, nodes):
    if i == 0:
        return None

    for index in range(i-1, -1, -1):
        if isinstance(nodes[index], Branch):
            return index
    return None

def is_last_in_branch(i, nodes):
    if i == 0 or i == (len(nodes) - 1):
        return True

    if isinstance(nodes[i], Leaf):
        return not are_siblings(i, i+1, nodes)

    parent_index = find_parent(i, nodes) 
    assert(parent_index is not None)
    return i == (parent_index + len(nodes[parent_index].branches))

def peek_right(i, nodes):
    if i == 0 or i == (len(nodes) - 1):
        return None

    if is_last_in_branch(i, nodes):
        return i+1 

    for index in range(i+1, len(nodes)):
        if are_siblings(index, i, nodes):
            return index

def main():
    # Assume list is sorted in lexicographic order
    nodes = [Branch("0"       , [0, 1, 2, 3]), # 0
             Branch("00"      , [1, 2]      ), # 1
             Leaf  ("00131211"              ), # 2
             Leaf  ("00211002"              ), # 3
             Branch("01"      , [0, 2, 3]   ), # 4
             Leaf  ("01013302"              ), # 5
             Leaf  ("01202113"              ), # 6
             Leaf  ("01321132"              ), # 7
             Leaf  ("02112220"              ), # 8
             Leaf  ("03322130"              )] # 9

    assert(peek_left(0, nodes) == None)
    assert(peek_left(1, nodes) == None)
    assert(peek_left(2, nodes) == None)
    assert(peek_left(3, nodes) == 2)
    assert(peek_left(4, nodes) == 1)
    assert(peek_left(5, nodes) == 1)
    assert(peek_left(6, nodes) == 5)
    assert(peek_left(7, nodes) == 6)
    assert(peek_left(8, nodes) == 4)
    assert(peek_left(9, nodes) == 8)

    assert(peek_right(0, nodes) == None)
    assert(peek_right(1, nodes) == 4)
    assert(peek_right(2, nodes) == 3)
    assert(peek_right(3, nodes) == 4)
    assert(peek_right(4, nodes) == 8)
    assert(peek_right(5, nodes) == 6)
    assert(peek_right(6, nodes) == 7)
    assert(peek_right(7, nodes) == 8)
    assert(peek_right(8, nodes) == 9)
    assert(peek_right(9, nodes) == None)


if __name__ == "__main__":
    main()
