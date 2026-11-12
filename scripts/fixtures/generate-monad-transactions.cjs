// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// Run with a path to the viem-monad package built from the reference SDK revision.
const fs = require('node:fs');
const path = require('node:path');
const { createRequire } = require('node:module');
const sdk = createRequire(path.resolve(process.argv[2], 'package.json'));
const { Transaction, Submission } = sdk('./_cjs/monad/index.js');
const { privateKeyToAccount } = sdk('./_cjs/accounts/index.js');
const account = privateKeyToAccount(`0x${'0'.repeat(63)}1`);
const to = '0x0000000000000000000000000000000000000002';
const base = { chainId: 20143n, nonce: 0n, gas: 21000n, to, value: 0n,
  maxPriorityFeePerGas: 2000000000n, maxFeePerGas: 50000000000n };
const cases = [
  ['draft-example', { chainId: 143n, nonce: 7n, value: 1000000000000000000n }],
  ['devnet-transfer', {}],
  ['empty-access-list', { accessList: [] }],
  ['access-list', { gas: 25300n, accessList: [{ address: to, storageKeys: [`0x${'0'.repeat(64)}`] }] }],
  ['creation', { to: undefined, data: '0x60006000f3', gas: 100000n }],
  ['wide-fees', { maxFeePerGas: 1n << 200n, maxPriorityFeePerGas: 1n << 140n }],
  ['max-nonce', { nonce: (1n << 64n) - 1n }],
  ['wide-chain-id', { chainId: 1n << 200n }],
];
(async () => {
  const vectors = [];
  for (const [name, changes] of cases) {
    const transaction = Transaction.from({ ...base, ...changes });
    const canonical = await Transaction.sign({ account, transaction });
    const signed = Transaction.deserialize(canonical);
    vectors.push({ name, sender: account.address.toLowerCase(), signingPayload: Transaction.serialize(transaction),
      signingHash: Transaction.getSignPayload(transaction), canonical, hash: Transaction.hash(signed),
      submission: Submission.serialize(signed) });
  }
  fs.writeFileSync(path.join(__dirname, '../../category/execution/ethereum/core/test/monad_type40_vectors.json'),
    JSON.stringify({ sdkRevision: '40e3a58c1c8c9c0326558eee8991992173059ea4', vectors }, null, 2) + '\n');
})().catch(error => { console.error(error); process.exitCode = 1; });
