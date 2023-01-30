from siblings import longest_common_prefix
from nodes import Leaf, Branch
from enum import Enum

# merge the two nodes together
# either a new branch is created or branches are concatenated together
def merge(s_2, s_3):
    common_prefix = longest_common_prefix(s_2, s_3)
    
    if s_2.path == common_prefix:
        assert(isinstance(s_2, Branch))
        return Branch(s_2.path, s_2.branches + [s_3])
    
    return Branch(common_prefix, [s_2, s_3])

# Returns s_2 and s_3 merged, or None if no action
def transform(s_1, s_2, s_3, s_4):
    assert(s_2 is not None and s_3 is not None)

    curr_prefix_len = len(longest_common_prefix(s_2, s_3))
    if (s_1 is None or curr_prefix_len > len(longest_common_prefix(s_1, s_2))) and \
            (s_4 is None or curr_prefix_len >= len(longest_common_prefix(s_3, s_4))):
        return merge(s_2, s_3)
    
    return None

def main():
    # merge two leaves together
    assert(transform(None                    , Leaf("1234"), Leaf("1235"), None)         == Branch("123", [Leaf("1234"), Leaf("1235")]))
    assert(transform(Branch("12", ["1", "2"]), Leaf("1234"), Leaf("1235"), None)         == Branch("123", [Leaf("1234"), Leaf("1235")]))
    assert(transform(None                    , Leaf("1234"), Leaf("1235"), Leaf("1237")) == Branch("123", [Leaf("1234"), Leaf("1235")]))
    assert(transform(Branch("12", ["1", "2"]), Leaf("1234"), Leaf("1235"), Leaf("1237")) == Branch("123", [Leaf("1234"), Leaf("1235")]))

    # no action
    assert(transform(Branch("123", ["1", "2"]) , Leaf("1234") , Leaf("1235") , None)          == None)
    assert(transform(None                      , Leaf("12345"), Leaf("12356"), Leaf("12357")) == None)
    assert(transform(Branch("1234", ["1", "2"]), Leaf("12345"), Leaf("12356"), Leaf("12357")) == None)

    # extend a branch
    assert(transform(None       , Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1235") , None)                                       == Branch("123", [Leaf("1231"), Leaf("1232"), Leaf("1235")]))
    assert(transform(None       , Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1235") , Leaf("1236"))                               == Branch("123", [Leaf("1231"), Leaf("1232"), Leaf("1235")]))
    assert(transform(Branch("12", [Leaf("1212"), Leaf("1222")]), Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1235"), Leaf("1236")) == Branch("123", [Leaf("1231"), Leaf("1232"), Leaf("1235")]))

    # emitting new branch
    assert(transform(None                                     , Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")]), None)         == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")])]))
    assert(transform(Branch("1", [Leaf("1123"), Leaf("1211")]), Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")]), None)         == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")])]))
    assert(transform(None                                     , Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")]), Leaf("1256")) == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")])]))
    assert(transform(Branch("1", [Leaf("1123"), Leaf("1211")]), Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")]), Leaf("1256")) == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Branch("124", [Leaf("1241"), Leaf("1242")])]))

    assert(transform(None                                      , Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245"), None)         == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245")]))
    assert(transform(Branch("11", [Leaf("1112"), Leaf("1121")]), Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245"), None)         == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245")]))
    assert(transform(None                                      , Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245"), Leaf("1268")) == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245")]))
    assert(transform(Branch("11", [Leaf("1112"), Leaf("1121")]), Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245"), Leaf("1268")) == Branch("12", [Branch("123", [Leaf("1231"), Leaf("1232")]), Leaf("1245")]))

if __name__ == "__main__":
    main()
