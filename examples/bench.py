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
BENCHMARKS = [
	("elastic", []),
	("fixedPointInt", []),
	("manualPrice", []), # TODO: split monotonicity to another exe
	# ("nirn", []), # TODO: resurrect (commented out becuase slowjust slow)
	("tokent", []),
]

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
	completed = subprocess.run(["%s/%s.exe" % (EXAMPLES_BIN_DIR,bench_name), "sat %d" % saturation_bound] + convex_config,
							  capture_output=True)
	process_output = completed.stdout
	process_stderr = completed.stderr
	logger.info("%s terminated with output: %s" % (str(bench_config), process_output))
	logger.info("%s terminated with stderr: %s" % (str(bench_config), process_stderr))
	if process_stderr.strip():
		logger.error("Failed to execute benchmark %s. Mayday" % bench_config)
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

def bench():
	logger.info("Start bench")

	for bench_name, aux_data in BENCHMARKS:
		saturation_bound = 1
		use_convex = False
		bench_config = (bench_name, saturation_bound, use_convex)

		res_summary = multiple_runs_and_summarize(bench_config, NUM_RUNS)
		logger.info("Summary of %d runs of %s: %s" % (NUM_RUNS, bench_config, res_summary))

	logger.info("End bench")

def main():
	set_logger()
	bench()

if __name__ == "__main__":
	main()