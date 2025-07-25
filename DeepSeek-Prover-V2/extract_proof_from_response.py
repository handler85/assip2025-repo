import os
import argparse
from pathlib import Path

def process_lean_file(file_path: Path, dry_run: bool = False):
    """
    Processes a single .lean file according to the specified rules.

    Args:
        file_path (Path): The path to the .lean file.
        dry_run (bool): If True, prints actions without modifying the file.
    """
    print(f"--- Checking: {file_path.name}")

    try:
        original_content = file_path.read_text(encoding='utf-8')

        trigger_sequence = "### Complete Lean 4 Proof\n\n```lean4"
        if trigger_sequence not in original_content:
            print("    -> Skipping: Required trigger sequence not found.")
            return

        print("    -> Found trigger sequence. Preparing modifications...")

        modified_content = original_content

        detailed_statement = "### Detailed"
        if detailed_statement in modified_content:
            modified_content = modified_content.replace(
                detailed_statement,
                f"/- {detailed_statement}",
                1
            )
            print("    - Action: Added '/-' before '### Detailed'.")
        else:
            print("    - Warning: '### Detailed' not found, skipping this action.")


       
        replacement_sequence = "### Complete Lean 4 Proof\n\nlean4\n-/"
        if trigger_sequence in modified_content:
            modified_content = modified_content.replace(
                trigger_sequence,
                replacement_sequence,
                1
            )
            print("    - Action: Modified the 'Complete Proof' code block and added '-/'.")
        else:
            print("    - Warning: Trigger sequence disappeared during processing. Aborting modification.")
            return

       
        lines = modified_content.splitlines()
        last_line_index = -1
        for i in range(len(lines) - 1, -1, -1):
            if lines[i].strip():
                last_line_index = i
                break
        
        if last_line_index != -1 and lines[last_line_index].strip() == "```":
            modified_content = "\n".join(lines[:last_line_index])
            if modified_content:
                modified_content += "\n"
            print("    - Action: Removed the final '```' from the end of the file.")
        else:
            print("    - Warning: Final '```' not found at the end of the file. Skipping this action.")


        if dry_run:
            print("    -> DRY RUN: No changes were written to the file.")
        else:
            file_path.write_text(modified_content, encoding='utf-8')
            print("    -> SUCCESS: File has been modified and saved.")

    except Exception as e:
        print(f"    -> ERROR: Could not process file {file_path.name}. Reason: {e}")


def main():
    """
    Main function to parse arguments and iterate through the directory.
    """
    parser = argparse.ArgumentParser(
        description="A script to reformat specific Lean 4 proof files.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument(
        "directory",
        type=str,
        help="The path to the directory containing .lean files."
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Perform a dry run. The script will report what it would do\n"
             "but will not actually modify any files. HIGHLY RECOMMENDED FOR FIRST RUN."
    )

    args = parser.parse_args()
    directory_path = Path(args.directory)

    if not directory_path.is_dir():
        print(f"Error: The specified path '{args.directory}' is not a valid directory.")
        return

    print(f"Starting script in directory: {directory_path.resolve()}")
    if args.dry_run:
        print("\n*** DRY RUN MODE IS ENABLED. NO FILES WILL BE MODIFIED. ***\n")
    else:
        print("\n*** LIVE MODE IS ENABLED. FILES WILL BE MODIFIED. ***")
        print("*** Please ensure you have a backup of your files. ***\n")


    lean_files = list(directory_path.glob("*.lean"))

    if not lean_files:
        print("No .lean files found in the specified directory.")
        return
        
    for file_path in lean_files:
        process_lean_file(file_path, args.dry_run)
        print("-" * 20)

    print("Script finished.")


if __name__ == "__main__":
    main()