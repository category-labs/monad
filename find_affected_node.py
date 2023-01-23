from nodes import Leaf, Branch
from bisect import bisect_left
from siblings import longest_common_prefix

def parent_path(new_leaf, insort_index, nodes):
    assert(not new_leaf in nodes)

    if insort_index == 0:
        return 0

    left_common = longest_common_prefix(nodes[insort_index-1], new_leaf) 

    # no right node
    if insort_index == len(nodes):
        return left_common

    right_common = longest_common_prefix(nodes[insort_index], new_leaf)

    # new parent is the longest common prefix with the left and right nodes
    return right_common if len(left_common) < len(right_common) else left_common

def find_affected_node(updated_leaf, nodes):
    if len(nodes) == 0:
        return None

    if len(nodes) == 1:
        return 0

    insort_index = bisect_left(nodes,
                               updated_leaf.path,
                               key=lambda n: n.path)

    # modifying an existing leaf node
    if insort_index < len(nodes) and nodes[insort_index] == updated_leaf:
        return insort_index
    
    # return node that is modified
    return bisect_left(nodes,
                       parent_path(updated_leaf, insort_index, nodes),
                       hi=insort_index,
                       key=lambda n: n.path)

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

    assert(find_affected_node(Leaf("10131214"), nodes) == 0)
    assert(find_affected_node(Leaf("0 211002"), nodes) == 0)
    assert(find_affected_node(Leaf("04211002"), nodes) == 0)

    assert(find_affected_node(Leaf("00 13121"), nodes) == 1)
    assert(find_affected_node(Leaf("00313121"), nodes) == 1)

    assert(find_affected_node(Leaf("00121211"), nodes) == 2)
    assert(find_affected_node(Leaf("00141211"), nodes) == 2)
    assert(find_affected_node(Leaf("00131211"), nodes) == 2)
    assert(find_affected_node(Leaf("00131311"), nodes) == 2)
    assert(find_affected_node(Leaf("00131214"), nodes) == 2)
    assert(find_affected_node(Leaf("00131214"), nodes) == 2)

    assert(find_affected_node(Leaf("00211002"), nodes) == 3)
    assert(find_affected_node(Leaf("00211402"), nodes) == 3)

    assert(find_affected_node(Leaf("01421132"), nodes) == 4)
    assert(find_affected_node(Leaf("01 21132"), nodes) == 4)
    assert(find_affected_node(Leaf("01121132"), nodes) == 4)

    assert(find_affected_node(Leaf("01023302"), nodes) == 5)
    assert(find_affected_node(Leaf("01023301"), nodes) == 5)
    assert(find_affected_node(Leaf("01023401"), nodes) == 5)

    assert(find_affected_node(Leaf("01202113"), nodes) == 6)
    assert(find_affected_node(Leaf("01212113"), nodes) == 6)
    assert(find_affected_node(Leaf("01202114"), nodes) == 6)

    assert(find_affected_node(Leaf("01321132"), nodes) == 7)
    assert(find_affected_node(Leaf("01311132"), nodes) == 7)
    assert(find_affected_node(Leaf("01331132"), nodes) == 7)
    assert(find_affected_node(Leaf("01321152"), nodes) == 7)

    assert(find_affected_node(Leaf("02112220"), nodes) == 8)
    assert(find_affected_node(Leaf("02112320"), nodes) == 8)
    assert(find_affected_node(Leaf("02212320"), nodes) == 8)

    assert(find_affected_node(Leaf("03322130"), nodes) == 9)
    assert(find_affected_node(Leaf("03322140"), nodes) == 9)

if __name__ == "__main__":
    main()
