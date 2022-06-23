import time
import sys
import logging
import subprocess
import re
from dataclasses import dataclass
import typing
import statistics

EXAMPLES_BIN_DIR = "."
NUM_RUNS = 3

NIRN_NAME = "nirn"

BENCHMARKS = [
	("elastic", [r"upper \& lower", "5", "3", "382", "362"], ["\\checkmark"]),
	("fixedPointIntMulDiv", [r"upper \& lower", "0", "2", "362", "452"], ["\\checkmark"]),
	("fixedPointIntDivMul", [r"upper \& lower", "0", "2", "362", "452"], ["\\checkmark"]),
	("manualPrice", [r"upper \& lower", "3", "3", "223", "216"], ["\\checkmark"]),
	("manualPriceMonotone", [r"monotonicity", "6", "5", "223", "216"], ["\\checkmark"]),
	(NIRN_NAME, [r"upper", "10", "5", "1196", "2297"], ["\\checkmark"]), # TODO: resurrect (commented out because slow)
	("tokent", [r"upper \& lower", "10", "4", "244", "558"], ["\\checkmark"]),
]

OUTPUT_BASIC_TABLE_PATH = "basic_table.tex"

BASIC_TABLE_HEADER_LATEX = r"""\begin{table}[t!]
	\centering
	{\small \caption{\label{Ta:Rewriting}
            {\small This table displays the results of the running the system on the examples. 
            Column 2 indicates the number of terms asked to rewrite for a given set of assumptions. \yf{remove?}
            Column 3 and 4 respectively give the number of equation and inequality assumptions (not including instantiated axioms) initially given. \yf{hardcoded numbers not up to date}
            Columns 5 and 6 respectively give the number of distinct monomials and inequalities generated from the saturated cone. 
            Column 7 gives the overall time in seconds to solve all queries. 
            Column 8 gives the time in seconds to saturate the cone. 
            Column 9 gives the time Z3 took to solve the final optimization problem given the resulting cone. 
            Column 10 displays whether the result of the system was useful. All experiments in this table were taken using a product saturation depth of 3. 
            \yf{manual price: monotone property has different number of eqs and ineqs}
	}}}
	\resizebox{.99\textwidth}{!}{
\begin{tabular}{|| l | l | r | r || r | r | r | r | r | c ||}
\hline
Benchmark name & \#t's & \#eq's & \#in's & \#m & \#in's & time & csat time & reduce time & res\\
\hline\hline
"""

BASIC_TABLE_TAIL_LATEX = r"""\end{tabular}
}
\end{table}
"""

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

def execute_benchmark(bench_config):
	(bench_name, saturation_bound, use_convex) = bench_config

	convex_config = ["-hull"] if use_convex else []
	logger.info("Executing %s. Saturation bound: %d. Use convex: %r" % (bench_name, saturation_bound, use_convex) )
	completed = subprocess.run(["%s/%s.exe" % (EXAMPLES_BIN_DIR,bench_name), "-sat", str(saturation_bound)] + convex_config,
							  capture_output=True)
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

def execute_and_summarize(bench_config):
	output = execute_benchmark(bench_config)
	prod_sat_time = get_time_by_keyword(r"prod sat", output)
	nimpl_sat_time = get_time_by_keyword(r"nimpl sat", output)
	reduce_eq_time = get_time_by_keyword(r"reduce eq", output)
	reduce_ineq_time = get_time_by_keyword(r"reduce ineq", output)
	rewrite_time = get_time_by_keyword(r"Rewrite \D*", output)

	csat_time = prod_sat_time + nimpl_sat_time
	reduce_time = reduce_eq_time + reduce_ineq_time

	total_time = rewrite_time # TODO: is this correct?

	return ExperimentSummary(bench_config, 1, csat_time, reduce_time, total_time)

def multiple_runs_and_summarize(bench_config, num_runs):
	assert num_runs >= 1
	summaries = [execute_and_summarize(bench_config) for _ in range(num_runs)]
	return ExperimentSummary(bench_config, 
							num_runs, 
							statistics.mean(s.csat_time for s in summaries),
							statistics.mean(s.reduce_time for s in summaries),
							statistics.mean(s.total_time for s in summaries))

def time_to_str(t):
	return str(round(t, 1))

def bench_basic_table(also_nirn=True):
	logger.info("Start bench")

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

	logger.info("End bench")

def main():
	set_logger()
	bench_basic_table()

if __name__ == "__main__":
	main()