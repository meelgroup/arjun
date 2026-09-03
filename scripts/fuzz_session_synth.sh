#!/bin/bash
#
# Create a tmux session with multiple fuzzing windows running fuzz.py
#
# Usage:
#   ./fuzz_session.sh [--num N] [fuzz.py options]
#
# Options:
#   --num N    Number of tmux windows to create (default: 24)
#
# Examples:
#   ./fuzz_session.sh                           # 24 windows, default options
#   ./fuzz_session.sh --num 8                   # 8 windows, default options
#
# All arguments (except --num) are forwarded to fuzz_synth.py in each window.

SESSION="fuzzing synth"
DIR="$(pwd)"
NUM_WINDOWS=24

# Parse --num argument if present
if [ "$1" = "--num" ]; then
  if [ -z "$2" ] || ! [[ "$2" =~ ^[0-9]+$ ]]; then
    echo "Error: --num requires a positive integer argument"
    exit 1
  fi
  NUM_WINDOWS=$2
  shift 2
fi

CMD="./fuzz_synth.py $@"

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
