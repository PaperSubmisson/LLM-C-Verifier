# Project Structure

- `main.py`: The main entry point of the verification pipeline (CEGIS loop, concurrent execution, and report generation).
- `benchmark/`: Contains the C language verification tasks.

# Prerequisites

Before running the tool, ensure the following dependencies are installed and properly configured in your system environment.

# 1. Python Dependencies
The framework requires Python 3.8 or higher. Standard libraries (`os`, `re`, `subprocess`, `concurrent.futures`, etc.) are used alongside the following external packages. Install them via `pip`:
pip install openai pycparser

# 2. Boogie and Z3 Solver
The tool relies on the Boogie intermediate verification language and the Z3 SMT solver.

Z3 Solver: Can be installed via package managers (e.g., apt install z3 on Ubuntu, brew install z3 on macOS) or downloaded from the official repository. Ensure the z3 executable is in your system's PATH.

Boogie: Requires the .NET SDK. The recommended way to install Boogie is via the dotnet tool:

dotnet tool install --global boogie

Ensure the boogie command is globally accessible in your PATH. For manual installation, refer to the Boogie GitHub repository.

# 3. GCC Compiler
Required for the dynamic analysis phase to compile and execute C programs to verify the presence of assertion failures. Ensure gcc is available in your PATH.

# Configuration
Before running the framework, configure the API settings in main.py. Locate the Config section at the top of the file:
# ================= Config section =================
API_KEY = "YOUR_API_KEY_HERE"        # [Required] Enter your LLM API key
BASE_URL = "https://api.openai.com/v1" # [Required] The base URL of the LLM API endpoint
MODEL_NAME = "gpt-4"                 # [Required] The specific model version to use
TARGET_FOLDER = "./benchmark/task1"  # The relative path to the directory containing C benchmarks
MAX_WORKERS = 150                    # Maximum number of concurrent verification threads
LOG_FOLDER = f"{TARGET_FOLDER}/logs" # Directory where verification logs and summaries will be saved
# ===========================================

# Usage
Execute the main script from the root directory:
python main.py

# Notes on High Concurrency
The framework uses concurrent.futures.ThreadPoolExecutor to process multiple verification tasks simultaneously. When MAX_WORKERS is set to a high value (e.g., 150), the script spawns numerous parallel subprocesses for Boogie and GCC, which consume a large number of file descriptors.

If you encounter Too many open files errors (OS Error 24) on Linux or macOS, you need to increase the system's file descriptor limit before running the script. Use the following command:
ulimit -n 10240
python main.py

# Output
The console will display a brief progress status for each task.

Detailed execution traces, Boogie outputs, and LLM interaction logs for each C file will be saved independently in the LOG_FOLDER (e.g., ./benchmark/task1/logs/task_name.c.log).

A final summary.txt will be generated in the LOG_FOLDER summarizing the verification results (e.g., SUCCESS, BUG_FOUND, TIMEOUT, SYNTAX_ERROR) for all files.