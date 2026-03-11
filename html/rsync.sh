#!/bin/bash
set -euxo pipefail

rsync -vaP arjun.js arjun.wasm  index.html msoos.org:/var/www/arjun/
