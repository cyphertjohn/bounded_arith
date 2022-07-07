import time
import sys
import logging
import subprocess
import re
from dataclasses import dataclass, fields, asdict
import typing
import statistics
import matplotlib.pyplot as plt
import numpy as np
import csv

def dict_union(d1, d2):
	return {**d1, **d2}

EXAMPLES_BIN_DIR = "."
NUM_RUNS_BASIC_TABLE = 3

NIRN_NAME = "nirn"

BENCHMARKS = [
	# ("elastic", ["5", "3", "3", "8", "814", "413"], []),
	("fixedPointInt", ["0", "2", "2", "2", "162", "131"], []),
	("manualPrice", ["3", "4", "1", "4", "163", "168"], []),
	("manualPriceMonotone", ["6", "5", "2", "8", "218", "228"], []),
	("tokent", ["10", "4", "3", "13", "815", "288"], []),
	(NIRN_NAME, ["10", "5", "6", "16", "4057", "1351"], [])
]

OUTPUT_BASIC_TABLE_PATH = "basic_table.tex"

BASIC_TABLE_HEADER_LATEX = r"""\begin{table}[t!]
	\centering
	{\small \caption{\label{Ta:Rewriting}
            {\small Performance of \Tool on the examples.  
            \#eq and \#ineq's are resp.\ equality and inequality assumptions initially given (not including instantiated axioms);
            \#floors is the number of integer divisions (floor of division) terms in the assumptions.
            \#c-eq and \#c-ineq are resp.\ the number of equalities/inequalities in the generated cone's ideal/polyhedron; \#m is the number of distinct monomials in the inequalities.
            time is the overall execution time of $\Tool$ (all times in seconds).
            csat is the time to saturate the cone. 
            reduce is the time to reduce w.r.t.\ the cone using local projection. 
            reduce-lp is the time to reduce using linear programming instead of local projection.
            All experiments in this table were taken using a product saturation depth of 3. 
	}}}
	\resizebox{.99\textwidth}{!}{
\begin{tabular}{|| l | r | r | r || r | r | r || r | r | r || r ||}
\hline
Benchmark name & \#eq & \#in & \#floors & \#c-eq & \#c-in & \#c-m & time (s) & csat (s) & reduce (s) & reduce-lp (s) \\
\hline\hline
"""

BASIC_TABLE_TAIL_LATEX = r"""\end{tabular}
}
\end{table}
"""

SATURATION_SCALABILITY_MAX_BOUND = 20
# SCALABILITY_TIMEOUT_SECONDS = 5
SCALABILITY_TIMEOUT_SECONDS = 10 * 60

BENCHMARKS_SATURATION_SCALABILITY_GRAPHICS_CONTROL = {
	"elastic": (3, "o"),
	"fixedPointInt": (3, "s"),
	"manualPrice": (2, "*"),
	"manualPriceMonotone": (2, "D"),
	"tokent": (3, "^"),
	NIRN_NAME: (3, "P")
}

OUTPUT_SATURATION_SCALABILITY_PLOT_PATH = "saturation_scalability.pdf"
OUTPUT_SATURATION_SCALABILITY_CSV_PATH = "saturation_scalability.csv"
OUTPUT_SATURATION_SCALABILITY_TABLE_PATH = "sat_size_table.tex"

NUM_RUNS_SATURATION_SCALABILITY = 3

SATURATION_SCALABILITY_TABLE_HEADER = r"""\begin{table}
	\centering
	{\small \caption{\label{Ta:SatScaleConeSize}
            {\small
            The size of the cone and run-time breakdown of each examples as the saturation depth is increased until a timeout of %(timeout)s minutes.
            \#c-eq and \#c-ineq are resp.\ the number of equalities/inequalities in the generated cone's ideal/polyhedron; \#m is the number of distinct monomials in the inequalities.
            time is the overall execution time of $\Tool$ (all times in seconds).
            csat is the time to saturate the cone. 
            reduce is the time to reduce w.r.t.\ the cone using local projection.
            -- indicates a timeout.
	}}}
"""
SATURATION_SCALABILITY_TABLE_TAIL = r"""\end{tabular}
\end{table}"""

global logger

@dataclass
class ExperimentSummary:
	bench_config: typing.Tuple[str, int, bool]
	nruns: int
	csat_time: float
	reduce_time: float
	total_time: float
	cone_eqs: float # integer unless averaged
	cone_ineqs: float # integer unless averaged
	cone_monomials: float # integer unless averaged

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
	(bench_name, saturation_bound, use_lp) = bench_config

	lp_config = ["-lp"] if use_lp else []
	logger.info("Executing %s. Saturation bound: %d. Use lp: %r" % (bench_name, saturation_bound, use_lp) )
	completed = subprocess.run(["%s/%s.exe" % (EXAMPLES_BIN_DIR,bench_name), "-sat", str(saturation_bound)] + lp_config,
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

def get_cone_size_from_log(output):
	match = re.search(r"Cone size: Num eqs: (\d+)\\n\s*Num ineqs: (\d+)\\n\s*Num of unique mons in ineqs: (\d+)", output)
	# match = re.search(r"Cone size: Num eqs: (\d+)\\n\s*Num ineqs:", output)
	if not match:
		return -1, -1, -1
	return int(match.group(1)), int(match.group(2)), int(match.group(3))

def execute_and_summarize(bench_config, timeout=None):
	output = execute_benchmark(bench_config, timeout=timeout)

	csat_time = get_time_by_keyword(r"Construct cone", output)
	reduce_time = get_time_by_keyword(r"Reducing", output)
	total_time = get_time_by_keyword(r"Rewrite.* total", output)

	cone_eqs, cone_ineqs, cone_monomials = get_cone_size_from_log(output)

	return ExperimentSummary(bench_config, 1, 
							csat_time, reduce_time, total_time,
							cone_eqs, cone_ineqs, cone_monomials)

def multiple_runs_and_summarize(bench_config, num_runs, timeout=None):
	assert num_runs >= 1
	summaries = [execute_and_summarize(bench_config, timeout=timeout) for _ in range(num_runs)]
	return ExperimentSummary(bench_config, 
							num_runs, 
							statistics.mean(s.csat_time for s in summaries),
							statistics.mean(s.reduce_time for s in summaries),
							statistics.mean(s.total_time for s in summaries),
							statistics.mean(s.cone_eqs for s in summaries),
							statistics.mean(s.cone_ineqs for s in summaries),
							statistics.mean(s.cone_monomials for s in summaries),)

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
			bench_config_local_project = (bench_name, saturation_bound, False)

			res_summary = multiple_runs_and_summarize(bench_config_local_project, NUM_RUNS_BASIC_TABLE)
			logger.info("Summary of %d runs of %s: %s" % (NUM_RUNS_BASIC_TABLE, bench_config_local_project, res_summary))

			bench_config_lp = (bench_name, saturation_bound, True)

			lp_res_summary = multiple_runs_and_summarize(bench_config_lp, NUM_RUNS_BASIC_TABLE)
			logger.info("Summary of %d runs of %s: %s" % (NUM_RUNS_BASIC_TABLE, bench_config_lp, res_summary))

			f.write(bench_name)
			f.write(" & ")
			f.write(" & ".join(aux_data_pre))
			f.write(" & ")
			f.write(time_to_str(res_summary.total_time))
			f.write(" & ")
			f.write(time_to_str(res_summary.csat_time))
			f.write(" & ")
			f.write(time_to_str(res_summary.reduce_time))
			f.write(" & ")
			f.write(time_to_str(lp_res_summary.reduce_time))
			if aux_data_post:
				f.write(" & ")
			f.write(" & ".join(aux_data_post))
			f.write("\\\\\n")
			f.write("\\hline\n")
			f.write("\n")

		f.write(BASIC_TABLE_TAIL_LATEX)

	logger.info("End bench basic table")

def bench_saturation_depth_scalability(also_nirn=True):
	logger.info("Start bench saturation depth scalability")

	with open(OUTPUT_SATURATION_SCALABILITY_CSV_PATH, "wt") as csv_log:
		w = csv.DictWriter(csv_log, ["name", "depth"] + [f.name for f in fields(ExperimentSummary)])
		w.writeheader()

		full_x_data = list(range(1, SATURATION_SCALABILITY_MAX_BOUND + 1))

		for bench_name, _, _ in BENCHMARKS:
			if (not also_nirn) and bench_name == NIRN_NAME:
				continue

			x_data = []
			y_data = []

			for i in full_x_data:
				saturation_bound = i
				use_lp = False
				bench_config = (bench_name, saturation_bound, use_lp)

				try:
					res_summary = multiple_runs_and_summarize(bench_config, NUM_RUNS_SATURATION_SCALABILITY, timeout=SCALABILITY_TIMEOUT_SECONDS)
					logger.info("Summary of %d runs of %s: %s" % (NUM_RUNS_SATURATION_SCALABILITY, bench_config, res_summary))

					w.writerow(dict_union({"name": bench_name, "depth": saturation_bound}, asdict(res_summary)))

					x_data.append(i)
					y_data.append(res_summary.total_time)

				except subprocess.TimeoutExpired:
					logger.info("Got timeout on %s" % str(bench_config))
					break


			success_depth, marker = BENCHMARKS_SATURATION_SCALABILITY_GRAPHICS_CONTROL[bench_name]
			success_x_index = full_x_data.index(success_depth)

			plt.plot(x_data, y_data, linestyle='--', marker=marker, label=bench_name)
			plt.plot(x_data[success_x_index], y_data[success_x_index], 'k'+marker, markersize=20, fillstyle='none', markeredgewidth=1.5)

		plt.xticks(full_x_data, full_x_data) # TODO: adjust full_x_data, full_y_data automatically
		plt.yticks(np.arange(0, SCALABILITY_TIMEOUT_SECONDS, SCALABILITY_TIMEOUT_SECONDS / 60 * 2)) 
		plt.xlabel("saturation depth")
		plt.ylabel("total time (s)")
		plt.legend()
		plt.savefig(OUTPUT_SATURATION_SCALABILITY_PLOT_PATH, bbox_inches='tight')

	logger.info("Start bench saturation depth scalability")

def experiment_summary_from_larger_dict(d):
	return ExperimentSummary(**{k: d[k] for k in (f.name for f in fields(ExperimentSummary))})

def str_time_to_str(s):
	if not s:
		return "--"
	else:
		return time_to_str(float(s))

def res_summary_or_fake_if_not_present(result_summaries, depth, bench_name):
	if (depth, bench_name) in result_summaries:
		return result_summaries[(depth, bench_name)]
	return ExperimentSummary(bench_config=(bench_name, depth, False),
							nruns="-1",
							csat_time=None,
							reduce_time=None,
							total_time=None,
							cone_eqs="--",
							cone_ineqs="--",
							cone_monomials="--")

def apply_to_all_depths_concat(bench_name, depths, result_summaries, fn):
		return " & ".join(fn(res_summary_or_fake_if_not_present(result_summaries, depth, bench_name))
						for depth in sorted(list(depths)))

def csv_to_saturation_depth_info_table():
	result_summaries = {}
	depths = set()

	with open(OUTPUT_SATURATION_SCALABILITY_CSV_PATH, "r") as csv_log:
		csv_dict_reader = csv.DictReader(csv_log)
		for row in csv_dict_reader:
			name = row['name']
			depth = row['depth']
			depths.add(depth)
			result_summaries[(depth, name)] = experiment_summary_from_larger_dict(row)

	with open(OUTPUT_SATURATION_SCALABILITY_TABLE_PATH, "wt") as f:
		f.write(SATURATION_SCALABILITY_TABLE_HEADER % {'timeout': SCALABILITY_TIMEOUT_SECONDS / 60})
		f.write(r"\begin{tabular}{|| c | l |" + (r"| c " * len(depths)) + "|}")
		f.write(r"\hline")
		f.write(r"\multicolumn{2}{| c |}{\multirow{2}{*}{Benchmark}} & \multicolumn{" + str(len(depths)) + "}{ | c | }{Saturation depth}\n")
		f.write("\\\\\n")
		f.write(r"\cline{3-%d}" % (len(depths) + 2))
		f.write(r"\multicolumn{2}{| c |}{} ")
		for i in sorted(list(depths)):
			f.write(" & " + i)
		f.write("\\\\\n")
		f.write("\\hline\\hline\n")

		for bench_name, _, _ in BENCHMARKS:				
			f.write(r"\multirow{6}{*}{%s} &" % bench_name)
			f.write(r"\#c-eq & ")
			f.write(apply_to_all_depths_concat(bench_name, depths, result_summaries, 
					lambda res_summary: str(res_summary.cone_eqs)))
			f.write("\\\\\n")
			f.write("\\cline{2-%d}\n" % (len(depths) + 2))

			f.write(" & ")
			f.write(r"\#c-ineq & ")
			f.write(apply_to_all_depths_concat(bench_name, depths, result_summaries, 
					lambda res_summary: str(res_summary.cone_ineqs)))
			f.write("\\\\\n")
			f.write("\\cline{2-%d}\n" % (len(depths) + 2))

			f.write(" & ")
			f.write(r" \#m & ")
			f.write(apply_to_all_depths_concat(bench_name, depths, result_summaries, 
					lambda res_summary: str(res_summary.cone_monomials)))
			f.write("\\\\\n")
			f.write("\\cline{2-%d}\n" % (len(depths) + 2))

			f.write(" & ")
			f.write(r" time & ")
			f.write(apply_to_all_depths_concat(bench_name, depths, result_summaries, 
					lambda res_summary: str_time_to_str(res_summary.total_time))) # str from csv
			f.write("\\\\\n")
			f.write("\\cline{2-%d}\n" % (len(depths) + 2))

			f.write(" & ")
			f.write(r" csat & ")
			f.write(apply_to_all_depths_concat(bench_name, depths, result_summaries, 
					lambda res_summary: str_time_to_str(res_summary.csat_time))) # str from csv
			f.write("\\\\\n")
			f.write("\\cline{2-%d}\n" % (len(depths) + 2))

			f.write(" & ")
			f.write(r" reduce & ")
			f.write(apply_to_all_depths_concat(bench_name, depths, result_summaries, 
					lambda res_summary: str_time_to_str(res_summary.reduce_time))) # str from csv
			f.write("\\\\\n")
			f.write("\\hline\\hline\n")

		f.write(SATURATION_SCALABILITY_TABLE_TAIL)

def main():
	set_logger()
	# bench_basic_table(also_nirn=True)
	# bench_saturation_depth_scalability(also_nirn=True)
	csv_to_saturation_depth_info_table()

if __name__ == "__main__":
	main()