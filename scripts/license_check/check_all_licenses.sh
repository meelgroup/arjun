#!/usr/bin/bash
set -x

check_license_fnames() {
    find "$1" -type f -name "$2" -exec ./licensecheck.pl -m {} \;
    NUM=$(find "$1" -type f -name "$2" -exec ./licensecheck.pl -m {} \; | grep -c UNK)
    echo "Number of files without license information: $NUM"
    if [ "$NUM" -ne 0 ]; then
        echo "There are some files without license information!"
        exit 255
    fi
}

check_license_fnames ../../src/ "*.cpp"
check_license_fnames ../../src/ "*.h"
check_license_fnames ../../src/ "*.hpp"
check_license_fnames ../../CMakeLists.txt
exit 0
