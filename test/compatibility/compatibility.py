import argparse
import os
import sys
import subprocess
import json
import shutil
from multiprocessing import Pool


def create_if_not_exists(directory):
    if not os.path.exists(directory):
        os.makedirs(directory)


def invoke_binary(binary_path, args):
    try:
        # Run the binary and capture the output
        process = subprocess.Popen(
            [binary_path] + args,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        stdout, stderr = process.communicate()

        # Wait for the process to finish and get the return code
        return_code = process.returncode

        return return_code, stdout, stderr
    except subprocess.CalledProcessError as e:
        print(f"Error while executing binary: {e}")
        return 1, "", ""


def prepare_output_directory(
        ethereum_tests_directory, test_suite_name, output_directory
):
    res = []
    print(ethereum_tests_directory, test_suite_name, output_directory)
    for root, dirs, files in os.walk(
            os.path.join(ethereum_tests_directory, test_suite_name)
    ):
        for name in files:
            if name.endswith(".json"):
                full_test_name = os.path.join(root, name)
                truncated_test_name = full_test_name[
                                      len(ethereum_tests_directory): -len(".json")
                                      ]

                resulting_directory = output_directory + truncated_test_name
                res.append(resulting_directory)

                create_if_not_exists(resulting_directory)

    return res


def parse_transaction_from_template(*, transaction_template, transaction_data):
    # TODO: parse different transaction types
    return {
        "input": transaction_template["data"][transaction_data["indexes"]["data"]],
        "gas": transaction_template["gasLimit"][transaction_data["indexes"]["gas"]],
        "gasPrice": transaction_template["gasPrice"],
        "nonce": transaction_template["nonce"],
        "to": transaction_template["to"],
        "value": transaction_template["value"][transaction_data["indexes"]["value"]],
        "v": "0x0",
        "r": "0x0",
        "s": "0x0",
        "secretKey": transaction_template["secretKey"],
        "hash": "0x0000000000000000000000000000000000000000000000000000000000000000",
        "sender": transaction_template["sender"],
    }


ALLOWED_FORK_NAMES = {
    "frontier",
    "homestead",
    "spurious_dragon",
    "byzantium",
    "constantinople",
    "istanbul",
    "berlin",
    "london",
}


def generate_input_files(
        *, num_workers, ethereum_tests_directory, output_directory, test_directories
):
    failed_test_directories = 0
    successful_test_directories = []
    for test_directory in test_directories:
        json_source_path = (
                ethereum_tests_directory + test_directory[len(output_directory):] + ".json"
        )

        if (
                "stCreateTest/CreateOOGafterMaxCodesize" in test_directory
                or "stQuadraticComplexityTest/Call50000_sha256" in test_directory
                or "stTimeConsuming/static_Call50000_sha256" in test_directory
                or "stTimeConsuming/CALLBlake2f_MaxRounds" in test_directory
                or "VMTests/vmPerformance" in test_directory
        ):
            print("Skipping time consuming test", test_directory)
            continue

        try:
            with open(json_source_path, "r") as f:
                input_directory = os.path.join(test_directory, "input")
                test_output_directory = os.path.join(test_directory, "output")

                create_if_not_exists(input_directory)
                create_if_not_exists(test_output_directory)

                json_source = json.load(f)
                data = json_source[list(json_source.keys())[0]]

                # dump env
                with open(os.path.join(input_directory, "env.json"), "w+") as env:
                    # deleting the `currentRandom` field ensures that geth does not override the specified fork to use
                    # the fork after the Merge
                    del data["env"]["currentRandom"]
                    json.dump(data["env"], env, indent=2)

                # dump pre state
                with open(os.path.join(input_directory, "alloc.json"), "w+") as alloc:
                    json.dump(data["pre"], alloc, indent=2)

                # dump transactions
                transaction_template = data["transaction"]
                for fork_name, transaction_list in data["post"].items():
                    lower_case_fork_name = fork_name.lower()
                    if lower_case_fork_name in ALLOWED_FORK_NAMES:
                        fork_directory = input_directory + "/" + lower_case_fork_name
                        create_if_not_exists(fork_directory)
                transactions_directory = os.path.join(input_directory, "transactions")
                create_if_not_exists(transactions_directory)

                for index, transaction_data in enumerate(
                        data["post"][list(data["post"].keys())[0]]
                ):
                    transaction = parse_transaction_from_template(
                        transaction_template=transaction_template,
                        transaction_data=transaction_data,
                    )
                    with open(
                            "{}/txn-{}.json".format(transactions_directory, str(index)),
                            "w+",
                    ) as transaction_fd:
                        json.dump([transaction], transaction_fd, indent=2)

            successful_test_directories.append(test_directory)
        except Exception as e:
            print(
                "Exception while handling {}. Removing {} from {}: {}".format(
                    json_source_path, test_directory, output_directory, str(e)
                )
            )
            shutil.rmtree(test_directory)
            failed_test_directories += 1

    print(
        "Successfully parsed {}/{} test directories.".format(
            len(test_directories) - failed_test_directories, len(test_directories)
        )
    )
    return successful_test_directories


def run_test(binary, arguments, test_output_directory):
    return_code, stdout, stderr = invoke_binary(binary, arguments)
    print("running", " ".join([binary] + arguments), "error code:", return_code)

    with open(os.path.join(test_output_directory, "stdout"), "w+") as f:
        f.write(stdout)
    with open(os.path.join(test_output_directory, "stderr"), "w+") as f:
        f.write(stderr)
    with open(os.path.join(test_output_directory, "return_code"), "w+") as f:
        f.write(str(return_code))
    with open(os.path.join(test_output_directory, "command"), "w+") as f:
        f.write(" ".join([binary] + arguments))


def run_tests(binary, test_directories):
    parallel_arguments = []
    for test_directory in test_directories:
        input_directory = os.path.join(test_directory, "input")
        test_output_directory = os.path.join(test_directory, "output")
        for fork_name in [
            x
            for x in os.listdir(input_directory)
            if os.path.isdir(os.path.join(input_directory, x)) and x != "transactions"
        ]:
            for transaction_name in os.listdir(
                    os.path.join(input_directory, "transactions")
            ):
                monad_output_directory = os.path.join(test_output_directory, "monad", fork_name, transaction_name)
                create_if_not_exists(monad_output_directory)
                compatibility_arguments = [
                    "--state.fork",
                    fork_name,
                    "--input.alloc",
                    os.path.join(input_directory, "alloc.json"),
                    "--input.env",
                    os.path.join(input_directory, "env.json"),
                    "--input.txs",
                    os.path.join(input_directory, "transactions", transaction_name),
                    "--output.directory",
                    monad_output_directory,
                ]
                parallel_arguments.append(
                    (binary, compatibility_arguments, monad_output_directory)
                )

    with Pool(processes=40) as pool:
        return pool.starmap(run_test, parallel_arguments)


def main():
    parser = argparse.ArgumentParser(
        description="A simple script to execute ethereum tests using a binary."
    )
    parser.add_argument(
        "--bin", required=True, type=str, help="Path to compatibility binary."
    )
    parser.add_argument(
        "--ethereum_tests",
        required=True,
        type=str,
        help="Path to ethereum tests repository.",
    )
    parser.add_argument(
        "--test_suite",
        required=True,
        type=str,
        help="Name of test folder (example GeneralStateTests)",
    )
    parser.add_argument(
        "--output_directory",
        required=True,
        type=str,
        help="Name of folder to dump output in",
    )

    args = parser.parse_args()

    if not os.path.isdir(args.ethereum_tests):
        print("path to ethereum tests " + args.ethereum_tests + " does not exist.")
        sys.exit(1)

    if os.path.exists(args.output_directory):
        if not os.path.isdir(args.output_directory):
            print(
                "Value passed into --output_directory ({}) already exists and is not a directory. Remove it and try "
                "again.".format(args.output_directory)
            )
            sys.exit(1)
    else:
        os.mkdir(args.output_directory)

    test_directories = prepare_output_directory(
        args.ethereum_tests, args.test_suite, args.output_directory
    )

    successful_test_directories = generate_input_files(
        num_workers=1,
        ethereum_tests_directory=args.ethereum_tests,
        output_directory=args.output_directory,
        test_directories=test_directories,
    )

    results = run_tests(args.bin, successful_test_directories)
    print("finished", len(results), "tests")


if __name__ == "__main__":
    main()
