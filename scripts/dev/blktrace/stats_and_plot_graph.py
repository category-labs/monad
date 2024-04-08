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
