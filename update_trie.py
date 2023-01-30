from nodes import Leaf, Branch
from peek import WorkIndex, peek_left_from_first_work, peek_left_no_work, peek_right

def generate_transformation_list(work, nodes):
    if len(work) == 0:
        return []

    prepend = peek_left_from_first_work(work[0], nodes)
    transformation = []

    while prepend is not None:
        transformation.insert(0, prepend)
        prepend = peek_left_no_work(transformation[0], nodes)

    current_work_index = WorkIndex(0)
    transformation.append(current_work_index)
    append = peek_right(transformation[-1], current_work_index, work, nodes)

    while append is not None:
        if isinstance(append, WorkIndex):
            current_work_index = append

        transformation.append(append)
        append = peek_right(transformation[-1], current_work_index, work, nodes)
        
    return list(map(lambda index: nodes[index] \
            if isinstance(index, int) \
            else work[int(index)], transformation))

def main():
    nodes = [Branch("45", [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])]),
             Leaf("4511"),
             Branch("452", [Leaf("4521"), Leaf("4522")]),
             Leaf("4521"),
             Leaf("4522")]

    assert(generate_transformation_list([Leaf("4501"), Leaf("4523")], nodes)
           == [Leaf("4501"), Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")]), Leaf("4523")])
    assert(generate_transformation_list([Leaf("4501")], nodes)
           == [Leaf("4501"), Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])])
    assert(generate_transformation_list([Leaf("4523")], nodes)
           == [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")]), Leaf("4523")])
    assert(generate_transformation_list([Leaf("6789")], nodes) ==
           [Branch("45", [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])]), Leaf("6789")])
    assert(generate_transformation_list([Leaf("4531")], nodes) ==
           [Branch("45", [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])]), Leaf("4531")])

if __name__ == "__main__":
    main()

# work_list = [...]

# working = []
# peek_left from work_list[0] until reach None, push to working from None to work_list[0]
# peek_right from work_list[0] until reach None, push to working from work_list[0] to None
# every node in work_list should be in working
# reduce that list to root
