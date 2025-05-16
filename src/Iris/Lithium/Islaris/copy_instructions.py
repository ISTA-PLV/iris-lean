#!/usr/bin/env python3

import os
import shutil
import sys
import re

def main():
    # Source directory
    source_dir = "../../../../../islaris"

    # Check if source directory exists
    if not os.path.isdir(source_dir):
        print(f"Error: Source directory '{source_dir}' does not exist.")
        sys.exit(1)

    # Find all .isla files in the source directory and its subdirectories
    for root, _, files in os.walk(source_dir):
        for file in files:
            if file.endswith(".isla"):
                # Get the full path of the source file
                source_file = os.path.join(root, file)

                # Get the relative path from the source directory
                rel_path = os.path.relpath(source_file, source_dir)

                # Split the path into directory and filename
                dir_parts = rel_path.split(os.sep)
                # skip pkvm handler for now since it uses parametric instructions
                if dir_parts[0] == "pkvm_handler":
                    continue
                original_file_name = os.path.splitext(dir_parts[-1])[0]
                capitalized_parts = [''.join(word.title() for word in part.split('_')) if part else part for part in dir_parts]
                target_file = os.sep.join(capitalized_parts)
                dir_name, _ = os.path.split(target_file)
                # Create the target directory with capitalized name if it doesn't exist
                if dir_name:
                    # print("makedirs: " + dir_name)
                    os.makedirs(dir_name, exist_ok=True)

                target_file = os.path.splitext(target_file)[0] + ".lean"

                print("from: " + source_file + " to: " + target_file)
                # Read the content of the source file
                with open(source_file, 'r') as f:
                    content = f.read()
                    content = re.sub(r';.*', '', content)

                # Write the content to the target file with the preamble
                with open(target_file, 'w') as f:
                    f.write("import Iris.Lithium.Islaris.Isla\n")
                    f.write("\n")
                    f.write(f"namespace Islaris.{dir_name.replace(os.sep, '.')}\n")
                    f.write("\n")
                    f.write("set_option maxRecDepth 30000 in\n")
                    f.write(f"def {original_file_name} : IslaTrace := isla(\n")
                    f.write(content)
                    f.write(")\n")

                print(f"Processed: {target_file} (from {rel_path})")

    print("All .isla files have been copied and modified successfully.")

if __name__ == "__main__":
    main()
