from nodes import Leaf, Branch
from bisect import bisect_left

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

    def __str__(self):
        return f"WorkIndex[{self.index}]"

    def __repr__(self):
        return self.__str__()

def is_first_in_branch(i, nodes):
    if i == 0:
        return False

    return isinstance(nodes[i-1], Branch)

# Peek left from pre-existing node. Does not take into consideration
# the work list
def peek_left_no_work(i, nodes):
    if i == 0:
        return None

    if is_first_in_branch(i, nodes):
        return peek_left_no_work(i-1, nodes)

    parent = find_parent(i, nodes)

    if parent is None:
        return None

    branch = bisect_left(nodes[parent].branches, nodes[i].path, key=lambda n:n.path)
    assert(nodes[parent].branches[branch] == nodes[i])
    assert(branch > 0)
    
    return bisect_left(nodes, nodes[parent].branches[branch-1].path, lo=parent, key=lambda n: n.path)

# given a prexisting node, find the index of the parent
def find_parent(i, nodes):
    if i == 0:
        return None

    target_path = parent_path(i, nodes)

    parent_index = bisect_left(nodes, target_path, hi=i, key=lambda n: n.path)

    assert(nodes[parent_index].path == target_path)
    assert(isinstance(nodes[parent_index], Branch))

    return parent_index

# Peek right from pre-existing node. Does not take into consideration
# the work list
def peek_right_no_work(i, nodes):
    if i == 0 or i == (len(nodes) - 1):
        return None

    parent = find_parent(i, nodes)

    assert(parent is not None)

    branch = bisect_left(nodes[parent].branches, nodes[i].path, key=lambda n:n.path)
    assert(nodes[parent].branches[branch] == nodes[i])

    # last in branch, look at parents right
    if branch == len(nodes[parent].branches)-1:
        return peek_right_no_work(parent, nodes)

    return bisect_left(nodes, nodes[parent].branches[branch+1].path, lo=parent, key=lambda n: n.path)

# Given a work item, find the path to its parent
# Note: this node may not exist
def get_parent_path_of_work(insort_index, work_item, nodes):
    parent_path = None
    if insort_index > 0:
        parent_path = longest_common_prefix(nodes[insort_index-1], work_item) 

    if insort_index < len(nodes):
        next_prefix = longest_common_prefix(nodes[insort_index], work_item)
        parent_path = next_prefix if len(next_prefix) > len(parent_path) else parent_path

    return parent_path

# given the first element in the work list, find the element to its left
def peek_left_from_first_work(work_item, nodes):
    assert(isinstance(work_item, Leaf))

    insort_index = bisect_left(nodes,
                               work_item.path,
                               key=lambda n: n.path)

    if insort_index < len(nodes) and nodes[insort_index] == work_item:
        return peek_left_no_work(insort_index, nodes)

    if insort_index == 0:
        return None

    parent_path = get_parent_path_of_work(insort_index, work_item, nodes)

    target_index = bisect_left(nodes, parent_path, key=lambda n: n.path)
    target = nodes[target_index]

    # parent exists
    if target.path == parent_path:
        branch_index = bisect_left(target.branches, work_item.path, key=lambda n: n.path)
        if branch_index == 0:
            return peek_left_no_work(target_index, nodes)
        elif branch_index == len(target.branches):
            return target_index
        else:
            return branch_index-1

    # parent does not exist
    return target_index if target.path < work_item.path else peek_left_no_work(target_index, nodes)

def peek_right(from_index, current_work_index, work, nodes):
    if isinstance(from_index, WorkIndex):
        return peek_right_from_work(from_index, work, nodes)
    return peek_right_from_node(from_index, current_work_index, work, nodes)

# Given the result of peeking right from the nodes list, look at the
# next work item and reconcile the two
def peek_right_common(right_from_nodes, work_index, work, nodes):
    if right_from_nodes is None:
        return None if work_index == (len(work)-1) else work_index+1 

    if work_index == (len(work)-1):
        return right_from_nodes

    next_work = work[int(work_index+1)]

    parent_path_of_next_work = get_parent_path_of_work(
            bisect_left(nodes, next_work.path, key=lambda n: n.path),
            next_work, nodes)
    branch_index = len(parent_path_of_next_work)

    while isinstance(nodes[right_from_nodes], Branch) and \
            next_work.path.startswith(nodes[right_from_nodes].path):

        node = nodes[right_from_nodes]

        # if work would be last element in branch, return the branch itself
        if parent_path_of_next_work == node.path and \
                node.branches[-1].path[branch_index] < next_work.path[branch_index]:
                return right_from_nodes

        right_from_nodes += 1

    return right_from_nodes if nodes[right_from_nodes].path < next_work.path else work_index+1

def peek_right_from_node(node_index, current_work_index, work, nodes):
    assert(isinstance(current_work_index, WorkIndex))

    right_from_nodes = peek_right_no_work(node_index, nodes)

    return peek_right_common(right_from_nodes, current_work_index, work, nodes)

def peek_right_from_work(work_index, work, nodes):
    assert(isinstance(work_index, WorkIndex))

    insort_index = bisect_left(nodes,
                               work[int(work_index)].path,
                               key=lambda n: n.path)

    if insort_index == len(nodes):
        return None if work_index == (len(work)-1) else work_index+1

    right_from_nodes = peek_right_no_work(insort_index, nodes) \
            if nodes[insort_index] == work[int(work_index)] \
            else insort_index

    return peek_right_common(right_from_nodes, work_index, work, nodes)

def main():
    # Assume list is sorted in lexicographic order
    nodes = [Branch("0"       , [Branch("00", [Leaf("00131211"), Leaf("00211002")]),
                                 Branch("01", [Leaf("01013302"), Leaf("01202113"), Leaf("01321132")]),
                                 Leaf("02112220"),
                                 Leaf("03322130")]),                                     # 0 
             Branch("00"      , [Leaf("00131211"), Leaf("00211002")]          ),         # 1
             Leaf  ("00131211"),                                                         # 2
             Leaf  ("00211002"),                                                         # 3
             Branch("01"      , [Leaf("01013302"), Leaf("01202113"), Leaf("01321132")]), # 4
             Leaf  ("01013302"),                                                         # 5
             Leaf  ("01202113"),                                                         # 6
             Leaf  ("01321132"),                                                         # 7
             Leaf  ("02112220"),                                                         # 8
             Leaf  ("03322130")]                                                         # 9

    # Sorted in lexicographic order by path
    assert(nodes == sorted(nodes, key=lambda n: n.path))

    assert(peek_left_no_work(0, nodes) == None)
    assert(peek_left_no_work(1, nodes) == None)
    assert(peek_left_no_work(2, nodes) == None)
    assert(peek_left_no_work(3, nodes) == 2)
    assert(peek_left_no_work(4, nodes) == 1)
    assert(peek_left_no_work(5, nodes) == 1)
    assert(peek_left_no_work(6, nodes) == 5)
    assert(peek_left_no_work(7, nodes) == 6)
    assert(peek_left_no_work(8, nodes) == 4)
    assert(peek_left_no_work(9, nodes) == 8)

    assert(peek_right_no_work(0, nodes) == None)
    assert(peek_right_no_work(1, nodes) == 4)
    assert(peek_right_no_work(2, nodes) == 3)
    assert(peek_right_no_work(3, nodes) == 4)
    assert(peek_right_no_work(4, nodes) == 8)
    assert(peek_right_no_work(5, nodes) == 6)
    assert(peek_right_no_work(6, nodes) == 7)
    assert(peek_right_no_work(7, nodes) == 8)
    assert(peek_right_no_work(8, nodes) == 9)
    assert(peek_right_no_work(9, nodes) == None)

    # Unit tests for work list peeking left with single element
    assert(peek_left_from_first_work(Leaf("13322130"), nodes) == 0)
    assert(peek_left_from_first_work(Leaf("04322130"), nodes) == 0)

    assert(peek_left_from_first_work(Leaf("02112220"), nodes) == 4)
    assert(peek_left_from_first_work(Leaf("02212220"), nodes) == 8)

    assert(peek_left_from_first_work(Leaf("01331132"), nodes) == 7)
    assert(peek_left_from_first_work(Leaf("01311132"), nodes) == 6)

    assert(peek_left_from_first_work(Leaf("0 123456"), nodes) == None)
    assert(peek_left_from_first_work(Leaf(" 0123456"), nodes) == None)
    assert(peek_left_from_first_work(Leaf("00121211"), nodes) == None)

    assert(peek_left_from_first_work(Leaf("01013302"), nodes) == 1)
    assert(peek_left_from_first_work(Leaf("01 13302"), nodes) == 1)
    assert(peek_left_from_first_work(Leaf("01023302"), nodes) == 5)

    # Unit tests for work list, peeking right
    assert(peek_right_from_work(WorkIndex(0), [Leaf("00311002"), Leaf("01421132")], nodes) == 4)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("01013302"), Leaf("01102113")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("01202113"), Leaf("01320132")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("01202113"), Leaf("01322132")], nodes) == 7)
    assert(peek_right_from_work(WorkIndex(0), [Leaf(" 1202113"), Leaf("01322132")], nodes) == 1)
    assert(peek_right_from_work(WorkIndex(0), [Leaf(" 1202113"), Leaf("00131211")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf(" 1202113"), Leaf("00231211")], nodes) == 2)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("00211002"), Leaf("02112220")], nodes) == 4)

    # -----------------------------------------------------------------

    nodes = [Branch("45", [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])]),
             Leaf("4511"),
             Branch("452", [Leaf("4521"), Leaf("4522")]),
             Leaf("4521"),
             Leaf("4522")]

    # Sorted in lexicographic order by path
    assert(nodes == sorted(nodes, key=lambda n: n.path))

    assert(peek_right_from_work(WorkIndex(0), [Leaf("4501"), Leaf("4522")], nodes) == 1)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("4511"), Leaf("4522")], nodes) == 3)
    assert(peek_right_from_work(WorkIndex(0), [Leaf("4511"), Leaf("4521")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("5511"), Leaf("5621")], nodes) == WorkIndex(1))
    assert(peek_right_from_work(WorkIndex(0), [Leaf("3511"), Leaf("4520")], nodes) == 1)
    
    assert(peek_right_from_node(1, WorkIndex(0), [Leaf("4501"), Leaf("4523")], nodes) == 2)
    assert(peek_right_from_node(1, WorkIndex(0), [Leaf("4501"), Leaf("4521")], nodes) == WorkIndex(1))

if __name__ == "__main__":
    main()
