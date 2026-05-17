#\!/bin/bash
#
# Create a tmux session with multiple fuzzing windows running the
# fuzz_interp_repair.py (Craig-interpolant repair).
#
# Usage:
#   ./fuzz_session_interp_repair.sh [--num N] [fuzzer options]
#
# Options:
#   --num N    Number of tmux windows to create (default: 24)
#
# Examples:
#   ./fuzz_session_interp_repair.sh                 # 24 windows, default options
#   ./fuzz_session_interp_repair.sh --num 16        # 16 windows, default options
#
# Run from the build/ directory. All arguments (except a leading --num,
# which sets the window count) are forwarded to the fuzzer in each window.

SESSION="fuzzing interp repair"
# Directory the script was invoked from (build/), not the symlink target.
DIR="$(cd "$(dirname "$0")" && pwd)"
NUM_WINDOWS=24

# Parse --num argument if present
if [ "$1" = "--num" ]; then
  if [ -z "$2" ] || \! [[ "$2" =~ ^[0-9]+$ ]]; then
    echo "Error: --num requires a positive integer argument"
    exit 1
  fi
  NUM_WINDOWS=$2
  shift 2
fi

CMD="../scripts/fuzz_interp_repair.py $@"

# Attach if session already exists
if tmux has-session -t "$SESSION" 2>/dev/null; then
  echo "Session '$SESSION' already exists, attaching..."
  tmux attach -t "$SESSION"
  exit 0
fi

echo "Creating tmux session with $NUM_WINDOWS windows..."

# Create session with first window
tmux new-session -d -s "$SESSION" -c "$DIR" -n "fuzz-1"
tmux send-keys -t "$SESSION:1" "$CMD" Enter

# Create remaining windows
for i in $(seq 2 $NUM_WINDOWS); do
  tmux new-window -t "$SESSION" -c "$DIR" -n "fuzz-$i"
  tmux send-keys -t "$SESSION:$i" "$CMD" Enter
done

# Select first window and attach
tmux select-window -t "$SESSION:1"
tmux attach -t "$SESSION"
