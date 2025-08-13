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

import pygal, sys, os, json, glob, re, pathlib, csv

path = os.path.join(os.path.dirname(__file__), 'histograms')
if len(sys.argv)>1:
  path = sys.argv[1]
jsonfiles = glob.glob(os.path.join(path, '*.json'))
jsonfiles.sort(key = lambda x: int(pathlib.Path(x).stem))
jsoncontents = []
for file in jsonfiles:
  with open(file) as ih:
    jsoncontents.append(json.load(ih))
x_labels = [ int(pathlib.Path(x).stem) for x in jsonfiles ]
x_labels = [ x + 500000 for x in x_labels ]

chart = pygal.Bar()
chart.title = 'History of total Ethereum transactions'
chart.x_title = 'block no region'
chart.y_title = 'count'
chart.x_labels = x_labels
chart.x_label_rotation = 90
chart.legend_at_bottom = True
chart.truncate_legend = -1
chart.add('total transactions', [x['total parsed transactions'] for x in jsoncontents])
chart.add('total accounts', [x['total accounts seen'] for x in jsoncontents])
chart.render_to_file('history.svg')

chart = pygal.StackedLine()
chart.title = 'Account share of total Ethereum transactions'
chart.x_title = 'block no region'
chart.y_title = '%'
chart.x_labels = x_labels
chart.x_label_rotation = 90
chart.legend_at_bottom = True
chart.truncate_legend = -1
accounts = []
r = re.compile('<= ([0-9]+)%')
for content in jsoncontents:
  l = []
  for k in content:
    m = r.match(k)
    if m:
      l.append(100.0*int(content[k])/content['total accounts seen'])
  accounts.append(l)
with open('out.csv', 'wt') as oh:
  writer = csv.writer(oh)
  for x in accounts:
    writer.writerow(x)
accounts = [ list(i) for i in zip(*accounts) ]
for i in range(0, len(accounts)):
  chart.add(f'<= {int((i+1)*100/len(accounts))}%', accounts[i])
chart.render_to_file('account_share.svg')
