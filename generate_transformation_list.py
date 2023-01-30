from nodes import Leaf, Branch
from peek import WorkIndex, peek_left_from_first_work, peek_left_no_work, peek_right

# Given a list of nodes to update (work) and pre-existing state (nodes),
# generate the transformation list for which to apply our transformation
# rules on
def generate_transformation_list(work, nodes):
    assert(len(work) > 0)

    prepend = peek_left_from_first_work(work[0], nodes)

    transformation = []

    while prepend is not None:
        assert(isinstance(prepend, int))
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
    assert(generate_transformation_list([Leaf("4511")], nodes) ==
           [Leaf("4511"), Branch("452", [Leaf("4521"), Leaf("4522")])])

    # -----------------------------------------------------------------------------------------------

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

    assert(generate_transformation_list([Leaf("00131211")], nodes) ==
           [Leaf("00131211"), Leaf("00211002"), Branch("01", [Leaf("01013302"), Leaf("01202113"), Leaf("01321132")]), Leaf("02112220"), Leaf("03322130")])
    assert(generate_transformation_list([Leaf("00311002")], nodes) ==
           [Branch("00", [Leaf("00131211"), Leaf("00211002")]), Leaf("00311002"), Branch("01", [Leaf("01013302"), Leaf("01202113"), Leaf("01321132")]), Leaf("02112220"), Leaf("03322130")])
    assert(generate_transformation_list([Leaf("00311002"), Leaf("01421122")], nodes) ==
           [Branch("00", [Leaf("00131211"), Leaf("00211002")]), Leaf("00311002"), Branch("01", [Leaf("01013302"), Leaf("01202113"), Leaf("01321132")]), Leaf("01421122"), Leaf("02112220"), Leaf("03322130")])
if __name__ == "__main__":
    main()
