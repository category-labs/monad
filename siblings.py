from nodes import Leaf, Branch

def longest_common_prefix(first, second):
    first = first.path
    second = second.path
    length = min(len(first), len(second))
    for i in range(length):
        if first[i] != second[i]:
            return first[:i]
    return first[:length]

def parent_path(i, nodes):
    if i == 0:
        return ""

    return longest_common_prefix(nodes[i], nodes[i-1])

def are_siblings(i, j, nodes):
    return parent_path(i, nodes) == parent_path(j, nodes)

def main():
    # Assume list is sorted in lexicographic order
    nodes = [Branch("0"       , ["0", "1", "2", "3"]), # 0
             Branch("00"      , ["1", "2"]          ), # 1
             Leaf  ("00131211"                      ), # 2
             Leaf  ("00211002"                      ), # 3
             Branch("01"      , ["0", "2", "3"]     ), # 4
             Leaf  ("01013302"                      ), # 5
             Leaf  ("01202113"                      ), # 6
             Leaf  ("01321132"                      ), # 7
             Leaf  ("02112220"                      ), # 8
             Leaf  ("03322130"                      )] # 9

    # Sorted in lexicographic order by path
    assert(nodes == sorted(nodes, key=lambda n: n.path))

    # Assert siblings
    assert(are_siblings(1, 4, nodes))
    assert(are_siblings(1, 8, nodes))
    assert(are_siblings(1, 9, nodes))
    assert(are_siblings(4, 8, nodes))
    assert(are_siblings(8, 9, nodes))
    assert(are_siblings(5, 6, nodes))
    assert(are_siblings(6, 7, nodes))

    # Assert not siblings
    assert(not are_siblings(1, 2, nodes))
    assert(not are_siblings(1, 5, nodes))
    assert(not are_siblings(1, 7, nodes))
    assert(not are_siblings(1, 7, nodes))
    assert(not are_siblings(7, 8, nodes))

    # root is not siblings with anyone
    for i in range(1, len(nodes)):
        assert(not are_siblings(0, i, nodes))

if __name__ == "__main__":
    main()
