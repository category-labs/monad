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

#!/usr/bin/python
import csv, pygal, sys, re
import numpy as np
import pandas as pd

MAXLINES=1000000

pattern = re.compile(r'\((\s*\d+\s*)\)')

print(f"Reading {sys.argv[1]} ...")
data = []
with open(sys.argv[1], "r") as file:
    log_data = file.read()
    
data = [int(match.group(1)) for match in pattern.finditer(log_data)] 
# blktrace sometimes outputs latencies clearly uint64_t overflows, so filter those out
data = [x for x in data if x < 1000000000]

# stats
df = pd.DataFrame(data, columns=['latency'])
perc = [.25, .50, .75, .90, .99, .999]
print(df.describe(percentiles=perc).apply(lambda s: s.apply('{0:.2f}'.format)))
 
data = [int(match.group(1)) for match in pattern.finditer(log_data)][:MAXLINES]

print("Rendering ...")
chart = pygal.Line(stroke=False,logarithmic=True)
chart.title = 'i/o latencies'
chart.add('reads', data, dots_size=0.12)
chart.render_to_file('io_latencies.svg')

print("You may need to reduce MAXLINES in the script to get a SVG renderer to actually render io_latencies.svg")
