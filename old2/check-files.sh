#!/bin/bash

# Set the root directory 
ROOT_DIR="src/"

# Path to the exclude configuration file
CONFIG_FILE=$ROOT_DIR"exclude.conf"

# Excluded files
excluded_files=()

# Function to read the exclude configuration file and return a list of excluded files
get_excluded_files() {
    if [ ! -f "$CONFIG_FILE" ]; then
        echo "Error: $CONFIG_FILE does not exist!"
        exit 1
    fi
    while read -r line
    do
        echo "$line"
        excluded_files+=("$line")
    done < $CONFIG_FILE
    echo "Excluding: $CONFIG_FILE"
    echo "$excluded_files"
}

# Function to run Agda on all files except the excluded ones
check_included_files() {
    get_excluded_files
    # excluded_files=($(get_excluded_files))
    for agda_file in $(find "$ROOT_DIR" -name "*.agda"); do
        # Check if the file is in the excluded list
        if [[ ! " ${excluded_files[@]} " =~ " ${agda_file} " ]]; then
            echo "Typechecking $agda_file"
            agda "$agda_file"  || { echo "Error: Typechecking failed for $agda_file"; exit 1; }
        else
            echo "Skipping $agda_file (excluded)"
        fi
    done
}

# Run the script
check_included_files