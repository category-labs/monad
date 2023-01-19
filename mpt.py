class Leaf:
    def __init__(self, path):
        self.path = path

    def __str__(self):
        return f"Leaf[{self.path}]"

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if isinstance(other, Leaf):
            return self.path == other.path
        return False

class Branch:
    def __init__(self, path, branches):
        self.path = path
        self.branches = branches

    def __str__(self):
        return f"Branch[{self.path} {self.branches}]"

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if isinstance(other, Branch):
            return self.path == other.path and self.branches == other.branches
        return False

# in-memory mpt
# database tbd at a later date
"""
root = Branch("0",
              [Branch("00",
                      [Leaf("00131211"), Leaf("00211002")]),
               Branch("01",
                      [Leaf("01013302"), Leaf("01202113"), Leaf("01321132")]),
               Leaf("02112220"),
               Leaf("03322130")])
"""

root = Branch("1",
              [Leaf("11111"),
               Branch("12",
                      [Leaf("12222"),
                       Branch("123", [Leaf("12333"),
                                      Leaf("12344")])])])

# find parent of existing element
def find_parent(element):
    if root == element or isinstance(root, Leaf):
        return None
    return find_parent_helper(element, root)

def find_parent_helper(element, current):
    assert(element != current)
    assert(isinstance(current, Branch))

    branch = element.path[len(current.path)]
    for child in current.branches:
        if child == element:
            return current
        if child.path[len(current.path)] == branch:
            return find_parent_helper(element, child)

    return None

# find node that element would modify if added as a new leaf to the existing mpt
def find_target(element):
    if root is None:
        return None

    return find_target_helper(element, root)

def find_target_helper(element, current):
    assert(current is not None)

    # can not traverse anymore, reached a leaf node
    if isinstance(current, Leaf):
        return current

    # check extension part of the branch
    if not element.path.startswith(current.path):
        return current

    # extension part matches, check that child exists and traverse if so
    branch = element.path[len(current.path)]
    for child in current.branches:
        if child.path[len(current.path)] == branch:
            return find_target_helper(element, child)

    # no child exists, return current branch node
    return current

# retrieve the node to the left of the element in storage
def peek_left_from_storage(element, is_new_leaf):
    target = find_target(element) if is_new_leaf else find_parent(element)

    if target is None:
        return None

    # if target is a leaf or branchs path does not match, peeking left
    # either yields the target itself or whatever is to its left
    if isinstance(target, Leaf) or not element.path.startswith(target.path):
        assert(is_new_leaf)
        return target if target.path < element.path else peek_left_from_storage(target, False)

    # The returned insertion point i partitions the array a into two halves so that 
    # all(val < x for val in a[lo : i]) for the left side and all(val >= x for val
    # in a[i : hi]) for the right side.
    index = bisect.bisect_left(target.branches, element.path, key=lambda child: child.path)

    # if insertion point is the beginning, go up one level
    if index == 0:
        return peek_left_from_storage(target, False)

    # if index is at the end of the branches, then peeking left is just the branch itself
    if index == len(target.branches):
        return target

    return target.branches[index - 1]

# retrieve the node to the right of the element in storage
def peek_right_from_storage(element, is_new_leaf=False):
    # target is the node that would be modified given the updating of this element
    target = find_target(element) if is_new_leaf else find_parent(element)

    if target is None:
        return None

    # if target is a leaf or branchs path does not match, peeking right
    # either yields the target itself or whatever is to its right
    if isinstance(target, Leaf) or not element.path.startswith(target.path):
        assert(is_new_leaf)
        return target if element.path < target.path else peek_right_from_storage(target, False)

    # The returned insertion point i partitions the array a into two halves so that
    # all(val <= x for val in a[lo : i]) for the left side and all(val > x for val
    # in a[i : hi]) for the right side.
    index = bisect.bisect_right(target.branches, element.path, key=lambda child: child.path)

    return peek_right_from_storage(target, False) if index == len(target.branches) else target.branches[index]

print(peek_left_from_storage(Leaf("21111"), True))
