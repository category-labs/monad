# Take the json files produced by mce and convert it to CSV so it can be
# inserted into a SQL database. Processing the JSON files to csv and then
# importing it with the COPY command is much faster than inserting rows, even
# with batching.
#
# Usage: to_csv.py <contract_directory> <address_directory> <output_directory>
# The csv files are saved in the current directory.
#
# To insert the data into the database, use the following commands:
# Drop the database, if it already exists:
#   dropdb monad
# Create the database:
#   createdb monad
# Initialize db with the schema:
#   psql -d monad -f cmd/vm/mce/scripts/schema.sql
# Import the csv files:
#   psql --db monad -c "\copy contracts            FROM '~/evm_contracts/results/csv/contracts.csv'            WITH (FORMAT CSV)"
#   psql --db monad -c "\copy contract_addresses   FROM '~/evm_contracts/results/csv/contract_addresses.csv'   WITH (FORMAT CSV)"
#   psql --db monad -c "\copy basic_blocks         FROM '~/evm_contracts/results/csv/basic_blocks.csv'         WITH (FORMAT CSV)"
#   psql --db monad -c "\copy instructions         FROM '~/evm_contracts/results/csv/instructions.csv'         WITH (FORMAT CSV)"
#   psql --db monad -c "\copy instruction_operands FROM '~/evm_contracts/results/csv/instruction_operands.csv' WITH (FORMAT CSV)"
#   psql --db monad -c "\copy instruction_outputs  FROM '~/evm_contracts/results/csv/instruction_outputs.csv'  WITH (FORMAT CSV)"
# To drop all data and start fresh without recreating the database:
#   psql --db monad -c "TRUNCATE contracts CASCADE"

import csv
import glob
import json
import itertools
import os
import argparse

parser = argparse.ArgumentParser(description="Process contract and address JSON files.")
parser.add_argument( "contract_directory"
                   , help="Directory containing contract JSON files (from analyze-with-mce.sh).")
parser.add_argument( "address_directory"
                   , help="Directory containing address symlinks (code_address).")
parser.add_argument( "output_directory"
                   , help="Directory to save output CSV files.")
args = parser.parse_args()

contract_dir = args.contract_directory
address_dir = args.address_directory
output_dir = args.output_directory

contract_serial_id             = 0
contract_address_serial_id     = 0
blocks_serial_id               = 0
instructions_serial_id         = 0
instruction_operands_serial_id = 0
instruction_outputs_serial_id  = 0

contract_ids = {} # Maps contract addresses to their IDs

# Return list of contract blocks
def contract_blocks(contract_id, blocks):
  return [ (contract_id, ix, block["offset"], block["is_jump_dest"], block["terminator"], block.get("fallthrough_dest", None), block["code_size"])
           for ix, block in enumerate(blocks)
         ]

def add_serial_id(start, rows):
  return list([(ix, ) + row for ix, row in enumerate(rows, start=start)])

# Push, swap, dup and log instructions are represented with an opcode + index.
# We want to distinguish these instructions, so we reconstruct the actual opcode.
# There's an exception, push0 instructions are parsed as push1 0x0, so we do the
# inverse conversion (at risk of treating real push1 0x0 as push0).
def instruction_opcode(instruction):
  if instruction.get("immediate", None) == "0x0" and instruction.get("index", 0) == 1:
    return instruction["opcode"]
  else:
    return instruction["opcode"] + instruction.get("index", 0)

# Return a list of instructions objects to insert.
def contract_instructions(block_ids, blocks):
  return [ (block_id, instr_ix, instruction_opcode(instruction), instruction.get("immediate", None), instruction["code_size"])
           for block_id, block in zip(block_ids, blocks)
           for instr_ix, instruction in enumerate(block["instructions"])
         ]

# Concatenate instructions from all blocks, so they can be inserted all at once.
def all_instructions(blocks):
  return itertools.chain(
    (instruction for block in blocks for instruction in block["instructions"])
  )

def contract_instruction_operands(instruction_ids, blocks):
  return [ ( instruction_id
           , operand_ix
           , operand.get("literal", None)
           , operand.get("general_reg", None)
           , operand.get("avx_reg", None)
           , operand.get("stack_offset", None)
           , "deferred_comparison" in operand
           , operand.get("bit_upper_bound", None))
           for instruction_id, instruction in zip(instruction_ids, all_instructions(blocks))
           for operand_ix, operand in enumerate(instruction.get("operands", []))
         ]

def contract_instruction_outputs(instruction_ids, blocks):
  return [ ( instruction_id
           , output_ix
           , output.get("literal", None)
           , output.get("general_reg", None)
           , output.get("avx_reg", None)
           , output.get("stack_offset", None)
           , "deferred_comparison" in output
           , output.get("bit_upper_bound", None))
           for instruction_id, instruction in zip(instruction_ids, all_instructions(blocks))
           for output_ix, output in enumerate(instruction.get("outputs", []))
         ]

def process_contract(handles, hash, contract):
  blocks = contract["basic_blocks"]
  contract_code_size = contract["code_size"]
  contract_bytecode_size = contract["bytecode_size"]
  global contract_serial_id
  contract_id = contract_serial_id
  contract_serial_id += 1

  contract_ids[hash] = contract_id # Keep track of contract ids

  global blocks_serial_id
  blocks_rows = add_serial_id(blocks_serial_id, contract_blocks(contract_id, blocks))
  blocks_serial_id += len(blocks_rows)
  block_ids = (i[0] for i in blocks_rows)

  global instructions_serial_id
  instructions_rows = add_serial_id(instructions_serial_id, contract_instructions(block_ids, blocks))
  instructions_serial_id += len(instructions_rows)
  instruction_ids = list(i[0] for i in instructions_rows)

  global instruction_operands_serial_id
  instruction_operands_rows = add_serial_id(instruction_operands_serial_id, contract_instruction_operands(instruction_ids, blocks))
  instruction_operands_serial_id += len(instruction_operands_rows)

  global instruction_outputs_serial_id
  instruction_outputs_rows = add_serial_id(instruction_outputs_serial_id, contract_instruction_outputs(instruction_ids, blocks))
  instruction_outputs_serial_id += len(instruction_outputs_rows)

  # Write to disk
  handles["contracts"].writerow([contract_id, hash, contract_code_size, contract_bytecode_size])
  handles["blocks"].writerows(blocks_rows)
  handles["instructions"].writerows(instructions_rows)
  handles["instruction_operands"].writerows(instruction_operands_rows)
  handles["instruction_outputs"].writerows(instruction_outputs_rows)

  return f"{contract_id}/{len(blocks_rows)}/{len(instructions_rows)}/{len(instruction_operands_rows)}/{len(instruction_outputs_rows)}"

def parse_json(file_name):
  with open(file_name, "r") as f:
    return json.load(f)

# List .json files in contract_dir
json_files=glob.glob(f"{contract_dir}/*.json")
with         open(f"{output_dir}/contracts.csv",            'w', newline='') as contracts_file:
  with       open(f"{output_dir}/basic_blocks.csv",         'w', newline='') as blocks_file:
    with     open(f"{output_dir}/instructions.csv",         'w', newline='') as instructions_file:
      with   open(f"{output_dir}/instruction_operands.csv", 'w', newline='') as operands_file:
        with open(f"{output_dir}/instruction_outputs.csv",  'w', newline='') as outputs_file:
          handles = {
              "contracts": csv.writer(contracts_file, quoting=csv.QUOTE_MINIMAL, quotechar='\''),
              "blocks": csv.writer(blocks_file, quoting=csv.QUOTE_NONE, quotechar='\''),
              "instructions": csv.writer(instructions_file, quoting=csv.QUOTE_MINIMAL, quotechar='\''),
              "instruction_operands": csv.writer(operands_file, quoting=csv.QUOTE_MINIMAL, quotechar='\''),
              "instruction_outputs": csv.writer(outputs_file, quoting=csv.QUOTE_MINIMAL, quotechar='\'')
          }
          for i, json_file in enumerate(json_files):
            # Contract hash is file name
            hash = json_file.split("/")[-1].split(".")[0]
            res = process_contract(handles, hash, parse_json(json_file))
            print(f"Process contract {json_file} ({i + 1}/{len(json_files)}) {res}")

# Process addresses:
# Addresses are symlinks in the code_address directories. The symlinks are named
# after the address that owns the contract, and points to the contract file
# named after the hash.
# We want a CSV file that maps each address to the contract id with the
# corresponding hash, using the contract_ids dictionary.

def lll(addresses_writer, dirname, verbose_depth = 0):
  acc = []
  for name in os.listdir(dirname):
    if name not in (os.curdir, os.pardir):
      full = os.path.join(dirname, name)
      if os.path.isdir(full) and not os.path.islink(full):
        if verbose_depth > 0:
          print(f"Descending into directory: {full}")
        lll(addresses_writer, full, verbose_depth = verbose_depth - 1)
      elif os.path.islink(full):
        _, address = os.path.split(full)
        _, hash = os.path.split(os.readlink(full))
        contract_id = contract_ids.get(hash, None)
        if contract_id is not None:
          global contract_address_serial_id
          acc.append((contract_address_serial_id, contract_id, address))
          contract_address_serial_id += 1

  addresses_writer.writerows(acc)

if address_dir is not None and address_dir != "":
  with open(f"{output_dir}/contract_addresses.csv", 'w', newline='') as addresses_file:
    addresses_writer = csv.writer(addresses_file, quoting=csv.QUOTE_MINIMAL, quotechar='\'')
    lll(addresses_writer, os.path.abspath(address_dir), verbose_depth = 2) # The function doesn't seem to work with relative paths
