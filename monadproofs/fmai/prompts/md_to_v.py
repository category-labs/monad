#!/usr/bin/env python3

import os
import argparse
#https://chatgpt.com/share/53b03f55-c37c-4346-bd66-52afe8f0d77d

def md_to_v(md_file_path, v_file_path):
    # Read the content of the .md file
    with open(md_file_path, 'r') as md_file:
        content = md_file.read()

    # Escape quotes
    escaped_content = content.replace('"', '""')

    # Compute the filename without extension
    src_filename_except_extension = os.path.splitext(os.path.basename(md_file_path))[0]

    # Prepare the Coq sentence
    coq_sentence = f'Ltac2 {src_filename_except_extension} () : string := "{escaped_content}".'

    # Write the Coq sentence to the .v file
    with open(v_file_path, 'w') as v_file:
        v_file.write("Require Import bluerock.ltac2.extra.extra.\n")
        v_file.write("From Ltac2 Require Import Ltac2.\n")
        v_file.write(coq_sentence)

    print(f"Converted {md_file_path} to {v_file_path}")

def main():
    parser = argparse.ArgumentParser(description='Convert a .md file to a .v file with a Coq Ltac2 string definition.')
    parser.add_argument('md_file', help='Path to the input .md file')
    parser.add_argument('v_file', help='Path to the output .v file')

    args = parser.parse_args()

    md_to_v(args.md_file, args.v_file)

if __name__ == "__main__":
    main()
