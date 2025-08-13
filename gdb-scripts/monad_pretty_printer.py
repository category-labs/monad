# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.


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


