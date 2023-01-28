from nodes import Leaf, Branch
from peek import WorkIndex, peek_left_from_first_work, peek_left_no_work, peek_right

#  # Try to merge with item on its right and return emitted nodes
#  def try_merge_right(work_index, work, nodes):
#      s_1 = peek_left_from_work(work_index, work, nodes)
#      s_2 = work_index
#      s_3 = peek_right_from_work(work_index, work, nodes)
#
#      if s_3 is None:
#          return None
#
#      s_4 = peek_right_from_work(s_3, work, nodes) \
#              if isinstance(s_3, WorkIndex) \
#              else peek_right_from_node(s_3, s_2, work, nodes)
#
#      result = transform(s_1, s_2, s_3, s_4)
#      if result is None:
#          return None
#
#      new_branch, action = result
#      parented_nodes = [s_3] if action == MergeAction.CONCATENATE else [s_2, s_3]
#      return new_branch, [node in parent_nodes if isinstance(node, WorkIndex)]
#
#  def try_merge_left_helper(target, current_work_index, work, nodes):
#      s_3 = target
#      s_4 = peek_right(target, current_work_index, work, nodes)
#      s_2 = peek_left(s_3, current_work_index, work, nodes)
#
#      if s_2 is None:
#          return None
#
#      s_1 = peek_left_from_work(s_2, work, nodes)
#
#      result = transform(s_1, s_2, s_3, s_4)
#
#      if result is None:
#          s_2 = try_merge_left_helper(s_2)
#      return result
#
#      if result is not None:
#          new_branch, action = result
#          parented_nodes = [s_3] if action == MergeAction.CONCATENATE else [s_2, s_3]
#          return new_branch, [node in parent_nodes if isinstance(node, WorkIndex)]
#
#      result = try_merge_left_helper(
#              s_2,
#              s_2 if isinstance(s_2, WorkIndex) else current_work_index,
#              work,
#              nodes)
#
#      if result is None:
#          return None
#
#      s_2, parented_nodes = result
#
#      result = transform(peek_left(s_2, s_2, work, nodes), s_2, s_3, s_4)
#      if result is None:
#          return None
#
#      new_branch, action = result
#      parented_nodes = [s_3] if action == MergeAction.CONCATENATE else [s_2, s_3]
#      return new_branch, parented_nodes + [node in parent_nodes if isinstance(node, WorkIndex)]
#
#  def try_merge_left(work_index, work, nodes):
#      return try_merge_left_helper(work_index, work_index, work, nodes)
#
#  # Returns a list of nodes that gets emitted as a result
#  def update_trie(nodes, work):
#      emit = []

def generate_working_nodes(work, nodes):
    if len(work) == 0:
        return []

    prepend = peek_left_from_first_work(WorkIndex(0), work, nodes)
    working_nodes = []

    while prepend is not None:
        working_nodes.insert(0, prepend)
        prepend = peek_left_no_work(working_nodes[0], nodes)

    current_work_index = WorkIndex(0)
    working_nodes.append(current_work_index)
    append = peek_right(working_nodes[-1], current_work_index, work, nodes)

    while append is not None:
        if isinstance(append, WorkIndex):
            current_work_index = append

        working_nodes.append(append)
        append = peek_right(working_nodes[-1], current_work_index, work, nodes)
        
    return list(map(lambda index: nodes[index] \
            if isinstance(index, int) \
            else work[int(index)], working_nodes))

def main():
    nodes = [Branch("45", [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])]),
             Leaf("4511"),
             Branch("452", [Leaf("4521"), Leaf("4522")]),
             Leaf("4521"),
             Leaf("4522")]

    print(generate_working_nodes([Leaf("4501"), Leaf("4523")], nodes))
    print(generate_working_nodes([Leaf("4501")], nodes))
    print(generate_working_nodes([Leaf("4523")], nodes))
    print(generate_working_nodes([Leaf("6789")], nodes))
    print(generate_working_nodes([Leaf("4531")], nodes))
    # Updating existing nodes
    #  assert(update_trie(nodes, [Leaf("4511")]) == [Leaf("4511"), Branch("45", ["1", "2"])])
    #  assert(update_trie(nodes, [Leaf("4521")]) == [Leaf("4521"), Branch("452", ["1", "2"]), Branch("45", ["1", "2"])])
    #  assert(update_trie(nodes, [Leaf("4522")]) == [Leaf("4521"), Branch("452", ["1", "2"]), Branch("45", ["1", "2"])])

if __name__ == "__main__":
    main()

# work_list = [...]

# working = []
# peek_left from work_list[0] until reach None, push to working from None to work_list[0]
# peek_right from work_list[0] until reach None, push to working from work_list[0] to None
# every node in work_list should be in working
# reduce that list to root
