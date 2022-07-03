import time
import sys
import logging
import subprocess
import re
from dataclasses import dataclass
import typing
import statistics
import matplotlib.pyplot as plt
import numpy as np

EXAMPLES_BIN_DIR = "."
NUM_RUNS = 3

NIRN_NAME = "nirn"

BENCHMARKS = [
	("elastic", ["5", "3", "382", "362"], ["\\checkmark"]),
	("fixedPointInt", ["0", "2", "362", "452"], ["\\checkmark"]),
	("manualPrice", ["3", "4", "223", "216"], ["\\checkmark"]),
	("manualPriceMonotone", ["6", "5", "223", "216"], ["\\checkmark"]),
	(NIRN_NAME, ["10", "5", "1196", "2297"], ["\\checkmark"]), # TODO: resurrect (commented out because slow)
	("tokent", ["10", "4", "244", "558"], ["\\checkmark"]),
]

OUTPUT_BASIC_TABLE_PATH = "basic_table.tex"

BASIC_TABLE_HEADER_LATEX = r"""\begin{table}[t!]
	\centering
	{\small \caption{\label{Ta:Rewriting}
            {\small This table displays the results of the running the system on the examples. 
            \#eq's and \#ineq's respectively give the number of equality and inequality assumptions (not including instantiated axioms) initially given. \yf{hardcoded numbers not up to date}
            \#c-m and \#c-in's respectively give the number of distinct monomials and inequalities generated from the saturated cone. 
            time gives the overall time in seconds to solve all queries. 
            csat time 8 gives the time in seconds to saturate the cone. 
            reduce time 9 gives the time to reduce w.r.t.\ the cone using the local projection method. 
            res displays whether the result of the system was useful. All experiments in this table were taken using a product saturation depth of 3. 
	}}}
	\resizebox{.99\textwidth}{!}{
\begin{tabular}{|| l | r | r || r | r | r | r | r | c ||}
\hline
Benchmark name & \#eq's & \#in's & \#c-m & \#c-in's & time & csat time & reduce time & res\\
\hline\hline
"""

BASIC_TABLE_TAIL_LATEX = r"""\end{tabular}
}
\end{table}
"""

SATURATION_SCALABILITY_MAX_BOUND = 7
SCALABILITY_TIMEOUT_SECONDS = 60

OUTPUT_SATURATION_SCALABILITY_PLOT_PATH = "saturation_scalability.png"

global logger

@dataclass
class ExperimentSummary:
	bench_config: typing.Tuple[str, int, bool]
	nruns: int
	csat_time: float
	reduce_time: float
	total_time: float

def set_logger():
	logging.basicConfig(format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
	                    datefmt='%H:%M:%S',
	                    level=logging.INFO,
	                    handlers=[
					        logging.FileHandler("%s-bench.log" % time.strftime("%Y%m%d-%H%M%S")),
					        logging.StreamHandler()
	    				])

	global logger
	logger = logging.getLogger(__name__)

def execute_benchmark(bench_config, timeout=None):
	(bench_name, saturation_bound, use_convex) = bench_config

	convex_config = ["-hull"] if use_convex else []
	logger.info("Executing %s. Saturation bound: %d. Use convex: %r" % (bench_name, saturation_bound, use_convex) )
	completed = subprocess.run(["%s/%s.exe" % (EXAMPLES_BIN_DIR,bench_name), "-sat", str(saturation_bound)] + convex_config,
							  capture_output=True,
							  timeout=timeout)
	process_output = completed.stdout
	process_stderr = completed.stderr
	logger.info("%s terminated with output: %s" % (str(bench_config), process_output))
	logger.info("%s terminated with stderr: %s" % (str(bench_config), process_stderr))
	if process_stderr.strip():
		logger.error("Failed to execute benchmark %s. Mayday" % str(bench_config))
		assert False

	return str(process_output)

def get_time_by_keyword(kwrd, output):
	float_re = r"\d*\.?\d+|\d+"
	match = re.search("%s: (%s) s" % (kwrd, float_re), output)
	if not match:
		logger.error("Could not find time of '%s' in %s. Mayday" % (kwrd, output))
		assert False
	return float(match.group(1))

def execute_and_summarize(bench_config, timeout=None):
	output = execute_benchmark(bench_config, timeout=timeout)

	csat_time = get_time_by_keyword(r"Construct cone", output)
	reduce_time = get_time_by_keyword(r"Reducing", output)
	total_time = get_time_by_keyword(r"Rewrite.* total", output)

	return ExperimentSummary(bench_config, 1, csat_time, reduce_time, total_time)

def multiple_runs_and_summarize(bench_config, num_runs, timeout=None):
	assert num_runs >= 1
	summaries = [execute_and_summarize(bench_config, timeout=timeout) for _ in range(num_runs)]
	return ExperimentSummary(bench_config, 
							num_runs, 
							statistics.mean(s.csat_time for s in summaries),
							statistics.mean(s.reduce_time for s in summaries),
							statistics.mean(s.total_time for s in summaries))

def time_to_str(t):
	return str(round(t, 1))

def bench_basic_table(also_nirn=True):
	logger.info("Start bench basic table")

	with open(OUTPUT_BASIC_TABLE_PATH, "wt") as f:

		f.write(BASIC_TABLE_HEADER_LATEX)

		for bench_name, aux_data_pre, aux_data_post in BENCHMARKS:
			if (not also_nirn) and bench_name == NIRN_NAME:
				continue

			saturation_bound = 3
			use_convex = False
			bench_config = (bench_name, saturation_bound, use_convex)

			res_summary = multiple_runs_and_summarize(bench_config, NUM_RUNS)
			logger.info("Summary of %d runs of %s: %s" % (NUM_RUNS, bench_config, res_summary))

			f.write(bench_name)
			f.write(" & ")
			f.write(" & ".join(aux_data_pre))
			f.write(" & ")
			f.write(time_to_str(res_summary.total_time))
			f.write(" & ")
			f.write(time_to_str(res_summary.csat_time))
			f.write(" & ")
			f.write(time_to_str(res_summary.reduce_time))
			if aux_data_post:
				f.write(" & ")
			f.write(" & ".join(aux_data_post))
			f.write("\\\\\n")
			f.write("\\hline\n")
			f.write("\n")

		f.write(BASIC_TABLE_TAIL_LATEX)

	logger.info("End bench basic table")

def bench_saturation_depth_scalability(also_nirn=True):
	logger.info("Start bench basic table")

	full_x_data = list(range(1, SATURATION_SCALABILITY_MAX_BOUND + 1))

	for bench_name, aux_data_pre, aux_data_post in BENCHMARKS:
		if (not also_nirn) and bench_name == NIRN_NAME:
			continue

		x_data = []
		y_data = []

		for i in full_x_data:
			saturation_bound = i
			use_convex = False
			bench_config = (bench_name, saturation_bound, use_convex)

			try:
				res_summary = multiple_runs_and_summarize(bench_config, NUM_RUNS, timeout=SCALABILITY_TIMEOUT_SECONDS)
				logger.info("Summary of %d runs of %s: %s" % (NUM_RUNS, bench_config, res_summary))

				x_data.append(i)
				y_data.append(res_summary.total_time)

			except subprocess.TimeoutExpired:
				logger.info("Got timeout on %s" % str(bench_config))
				break


		plt.plot(x_data, y_data, linestyle='--', marker='o', label=bench_name)

	plt.legend()
	plt.xticks(full_x_data, full_x_data)
	plt.yticks(np.arange(0, 60, 2)) 
	plt.xlabel("saturation bound")
	plt.ylabel("total time (s)")
	plt.savefig(OUTPUT_SATURATION_SCALABILITY_PLOT_PATH)

def main():
	set_logger()
	bench_basic_table(also_nirn=False)
	# bench_saturation_depth_scalability(also_nirn=False)

if __name__ == "__main__":
	main()