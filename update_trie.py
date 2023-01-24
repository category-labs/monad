from transform import transform
from peek import peek_left_from_work, peek_left_from_node, peek_right_from_work

def process_work(work_index, work, nodes):
    s_3 = work_index
    s_2 = peek_left_from_work(work_index, work, nodes)
    s_1 = None if isinstance(s_2, WorkIndex) else peek_left_from_node(s_2, nodes) 
    s_4 = peek_right_from_work(s_3, work, nodes)
    pass

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
