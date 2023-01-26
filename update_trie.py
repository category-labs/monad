from transform import transform, MergeAction
from peek import peek_left, peek_right

# Try to merge with item on its right and return emitted nodes
def try_merge_right(work_index, work, nodes):
    s_1 = peek_left_from_work(work_index, work, nodes)
    s_2 = work_index
    s_3 = peek_right_from_work(work_index, work, nodes)

    if s_3 is None:
        return None

    s_4 = peek_right_from_work(s_3, work, nodes) \
            if isinstance(s_3, WorkIndex) \
            else peek_right_from_node(s_3, s_2, work, nodes)

    result = transform(s_1, s_2, s_3, s_4)
    if result is None:
        return None

    new_branch, action = result
    parented_nodes = [s_3] if action == MergeAction.CONCATENATE else [s_2, s_3] 
    return new_branch, [node in parent_nodes if isinstance(node, WorkIndex)] 

def try_merge_left_helper(target, current_work_index, work, nodes):
    s_3 = target
    s_4 = peek_right(target, current_work_index, work, nodes)
    s_2 = peek_left(s_3, current_work_index, work, nodes)

    if s_2 is None:
        return None

    s_1 = peek_left_from_work(s_2, work, nodes)

    result = transform(s_1, s_2, s_3, s_4)

    if result is None:
        s_2 = try_merge_left_helper(s_2)
    return result

    if result is not None:
        new_branch, action = result
        parented_nodes = [s_3] if action == MergeAction.CONCATENATE else [s_2, s_3] 
        return new_branch, [node in parent_nodes if isinstance(node, WorkIndex)]

    result = try_merge_left_helper(
            s_2,
            s_2 if isinstance(s_2, WorkIndex) else current_work_index,
            work,
            nodes)

    if result is None:
        return None

    s_2, parented_nodes = result

    result = transform(peek_left(s_2, s_2, work, nodes), s_2, s_3, s_4)
    if result is None:
        return None

    new_branch, action = result
    parented_nodes = [s_3] if action == MergeAction.CONCATENATE else [s_2, s_3] 
    return new_branch, parented_nodes + [node in parent_nodes if isinstance(node, WorkIndex)]
    
def try_merge_left(work_index, work, nodes):
    return try_merge_left_helper(work_index, work_index, work, nodes)

# Returns a list of nodes that gets emitted as a result
def update_trie(nodes, work):
    emit = []

def main():
    nodes = [Branch("45", ["1", "2"]),
             Leaf("4511"),
             Branch("452", ["1", "2"]),
             Leaf("4521"),
             Leaf("4522")]

    # Updating existing nodes
    assert(update_trie(nodes, [Leaf("4511")]) == [Leaf("4511"), Branch("45", ["1", "2"])])
    assert(update_trie(nodes, [Leaf("4521")]) == [Leaf("4521"), Branch("452", ["1", "2"]), Branch("45", ["1", "2"])])
    assert(update_trie(nodes, [Leaf("4522")]) == [Leaf("4521"), Branch("452", ["1", "2"]), Branch("45", ["1", "2"])])

if __name__ == "__main__":
    main()


# while len(work) > 1 or (len(work) == 1 and isinstance(work[0], Leaf)):
#   for item in work:
#       try_merge_right(work)
# merge right -> if merged, update work list and new branch
# if merge right didnt work -> merge left
