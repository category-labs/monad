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
