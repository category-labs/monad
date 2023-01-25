from siblings import parent_path, are_siblings
from nodes import Leaf, Branch
from bisect import bisect_left

def is_first_in_branch(i, nodes):
    if i == 0:
        return False

    return isinstance(nodes[i-1], Branch)

# Peek left from pre-existing node. Does not take into consideration
# the work list
def peek_left_from_node(i, nodes):
    if i == 0:
        return None

    if is_first_in_branch(i, nodes):
        return peek_left_from_node(i-1, nodes)

    for index in range(i-1, 0, -1):
        if are_siblings(index, i, nodes):
            return index

    return None

def find_parent(i, nodes):
    if i == 0:
        return None

    target_path = parent_path(i, nodes)

    parent_index = bisect_left(nodes, target_path, hi=i, key=lambda n: n.path)

    assert(nodes[parent_index].path == target_path)
    assert(isinstance(nodes[parent_index], Branch))

    return parent_index

def is_last_in_branch(i, nodes):
    if i == 0 or i == (len(nodes) - 1):
        return True

    if isinstance(nodes[i], Leaf):
        return not are_siblings(i, i+1, nodes)

    parent_index = find_parent(i, nodes) 
    parent = nodes[parent_index]

    assert(parent_index is not None)

    branch = nodes[i].path[len(parent.path)]
    return parent.branches[-1] == branch

# Peek right from pre-existing node. Does not take into consideration
# the work list
def peek_right_helper(i, nodes):
    if i == 0 or i == (len(nodes) - 1):
        return None

    if is_last_in_branch(i, nodes):
        return i+1 

    for index in range(i+1, len(nodes)):
        if are_siblings(index, i, nodes):
            return index

    return None

class WorkIndex:
    def __init__(self, index):
        self.index = index

    def __sub__(self, other):
        if isinstance(other, WorkIndex):
            return WorkIndex(self.index - other.index)
        if isinstance(other, int):
            return WorkIndex(self.index - other) 

    def __add__(self, other):
        if isinstance(other, WorkIndex):
            return WorkIndex(self.index + other.index)
        if isinstance(other, int):
            return WorkIndex(self.index + other) 

    def __eq__(self, other):
        if isinstance(other, WorkIndex):
            return self.index == other.index
        if isinstance(other, int):
            return self.index == other

    def __int__(self):
        return self.index

def peek_left_from_work(work_index, work, nodes):
    assert(isinstance(work_index, WorkIndex))
    assert(isinstance(work[int(work_index)], Leaf))

    insort_index = bisect_left(nodes,
                               work[int(work_index)].path,
                               key=lambda n: n.path)
    if insort_index == 0:
        return None if work_index == 0 else work_index-1

    left_from_nodes = find_parent(len(nodes)-1, nodes) \
            if insort_index == len(nodes) \
            else peek_left_from_node(insort_index, nodes)

    if work_index == 0:
        return left_from_nodes
    
    last_work = work[int(work_index)-1]
    if isinstance(last_work, Branch):
        last_branch = last_work.branches[-1]
        if nodes[left_from_nodes].path[len(last_work.path)] <= last_branch:
            return work_index-1
        else:
            return left_from_nodes

    return work_index-1 if nodes[left_from_nodes].path <= last_work.path else left_from_nodes

# Given the result of peeking right from the nodes list, look at the
# next work item and reconcile the two
def peek_right_common(right_from_nodes, work_index, work, nodes):
    if work_index == (len(work)-1):
        return right_from_nodes

    next_work = work[int(work_index+1)]
    while isinstance(nodes[right_from_nodes], Branch) and \
            next_work.path.startswith(nodes[right_from_nodes].path):
        right_from_nodes += 1

    return right_from_nodes if nodes[right_from_nodes].path < next_work.path else work_index+1

def peek_right_from_node(node_index, last_processed_work, work, nodes):
    assert(isinstance(last_processed_work, WorkIndex))

    right_from_nodes = peek_right_helper(node_index, nodes)

    return peek_right_common(right_from_nodes, last_processed_work, work, nodes)

def peek_right_from_work(work_index, work, nodes):
    assert(isinstance(work_index, WorkIndex))

    insort_index = bisect_left(nodes,
                               work[int(work_index)].path,
                               key=lambda n: n.path)

    if insort_index == len(nodes):
        return None if work_index == (len(work)-1) else work_index+1

    right_from_nodes = peek_right_helper(insort_index, nodes) \
            if nodes[insort_index] == work[int(work_index)] \
            else insort_index

    return peek_right_common(right_from_nodes, work_index, work, nodes)

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

    assert(peek_left_from_node(0, nodes) == None)
    assert(peek_left_from_node(1, nodes) == None)
    assert(peek_left_from_node(2, nodes) == None)
    assert(peek_left_from_node(3, nodes) == 2)
    assert(peek_left_from_node(4, nodes) == 1)
    assert(peek_left_from_node(5, nodes) == 1)
    assert(peek_left_from_node(6, nodes) == 5)
    assert(peek_left_from_node(7, nodes) == 6)
    assert(peek_left_from_node(8, nodes) == 4)
    assert(peek_left_from_node(9, nodes) == 8)

    assert(peek_right_helper(0, nodes) == None)
    assert(peek_right_helper(1, nodes) == 4)
    assert(peek_right_helper(2, nodes) == 3)
    assert(peek_right_helper(3, nodes) == 4)
    assert(peek_right_helper(4, nodes) == 8)
    assert(peek_right_helper(5, nodes) == 6)
    assert(peek_right_helper(6, nodes) == 7)
    assert(peek_right_helper(7, nodes) == 8)
    assert(peek_right_helper(8, nodes) == 9)
    assert(peek_right_helper(9, nodes) == None)

    # Unit tests for work list peeking left with single element
    assert(peek_left_from_work(WorkIndex(0), [Leaf("13322130")], nodes) == 0)
    assert(peek_left_from_work(WorkIndex(0), [Leaf("04322130")], nodes) == 0)

    assert(peek_left_from_work(WorkIndex(0), [Leaf("02112220")], nodes) == 4)
    assert(peek_left_from_work(WorkIndex(0), [Leaf("02212220")], nodes) == 8)

    assert(peek_left_from_work(WorkIndex(0), [Leaf("01331132")], nodes) == 4)
    assert(peek_left_from_work(WorkIndex(0), [Leaf("01311132")], nodes) == 6)

    assert(peek_left_from_work(WorkIndex(0), [Leaf("0 123456")], nodes) == None)
    assert(peek_left_from_work(WorkIndex(0), [Leaf(" 0123456")], nodes) == None)
    assert(peek_left_from_work(WorkIndex(0), [Leaf("00121211")], nodes) == None)

    assert(peek_left_from_work(WorkIndex(0), [Leaf("01013302")], nodes) == 1)
    assert(peek_left_from_work(WorkIndex(0), [Leaf("01 13302")], nodes) == 1)
    assert(peek_left_from_work(WorkIndex(0), [Leaf("01023302")], nodes) == 5)

    # Unit tests for work list, peeking right
    assert(peek_right_from_work(WorkIndex(0), [Leaf("00311002"), Leaf("01421132")], nodes) == 5)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("01013302"), Leaf("01102113")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("01202113"), Leaf("01320132")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("01202113"), Leaf("01322132")], nodes) == 7)
    assert(peek_right_from_work(WorkIndex(0), [Leaf(" 1202113"), Leaf("01322132")], nodes) == 1)
    assert(peek_right_from_work(WorkIndex(0), [Leaf(" 1202113"), Leaf("00131211")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf(" 1202113"), Leaf("00231211")], nodes) == 2)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("00211002"), Leaf("02112220")], nodes) == 4)

    # -----------------------------------------------------------------

    nodes = [Branch("45", ["1", "2"]),
             Leaf("4511"),
             Branch("452", ["1", "2"]),
             Leaf("4521"),
             Leaf("4522")]

    # Sorted in lexicographic order by path
    assert(nodes == sorted(nodes, key=lambda n: n.path))

    assert(peek_right_from_work(WorkIndex(0), [Leaf("4501"), Leaf("4522")], nodes) == 1)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("4511"), Leaf("4522")], nodes) == 3)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("4511"), Leaf("4521")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("5511"), Leaf("5621")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("3511"), Leaf("4520")], nodes) == 1)
    
    assert(peek_right_from_node(1, WorkIndex(0), [Leaf("4501"), Leaf("4523")], nodes) == 3)
    assert(peek_right_from_node(1, WorkIndex(0), [Leaf("4501"), Leaf("4521")], nodes) == WorkIndex(1))

    assert(peek_left_from_work(WorkIndex(1), [Branch("45", ["0", "1"]), Leaf("4523")], nodes) == 2)
    assert(peek_left_from_work(WorkIndex(1), [Branch("45", ["0", "1"]), Leaf("4521")], nodes) == WorkIndex(0))

if __name__ == "__main__":
    main()
