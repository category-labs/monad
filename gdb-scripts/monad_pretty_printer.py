
import sys

# Add /usr/share/gcc to sys.path if it's not already there
if '/usr/share/gcc' not in sys.path:
    sys.path.append('/usr/share/gcc/python')

from libstdcxx.v6.printers import unique_ptr_get

def nibble_begin(val):
    return val['begin_nibble_'].cast(gdb.lookup_type('int'))

def nibble_size(val):
    return val['end_nibble_'] - nibble_begin(val)

def get_nibble(val, data, i):
    n = nibble_begin(val) + i
    c = data[n / 2]
    if n % 2 == 0:
        return c >> 4
    else:
        return c & 0xf

def nibble_to_string(val, data):
    if nibble_size(val) == 0:
        return '(empty)'
    s = '0x'
    for i in range(0, nibble_size(val)):
        s += '%x' % get_nibble(val, data, i)
    return s

class NibblesViewPrettyPrinter(gdb.ValuePrinter):
    "Print nibbles view"

    def __init__(self, val):
        size = nibble_size(val)
        if val.type.tag == 'monad::mpt::Nibbles':
            data = unique_ptr_get(val['data_'])
        else:
            data = val['data_']
        self.__values = [('size', size), ('value', nibble_to_string(val, data))]

    def children(self):
        return self.__values

    def num_children(self):
        return len(self.__values)

import gdb.printing

def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter("monad")
    pp.add_printer('NibblesView', 'monad::mpt::NibblesView$', NibblesViewPrettyPrinter)
    pp.add_printer('NibblesView', 'monad::mpt::Nibbles$', NibblesViewPrettyPrinter)
    return pp

try:
    gdb.printing.register_pretty_printer(gdb.current_objfile(), build_pretty_printer())
except:
    pass


