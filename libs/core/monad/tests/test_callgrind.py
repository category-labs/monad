from monad.tests import callgrind_parser

import fileinput
import json
from glob import glob
from os import path
from subprocess import check_output
from tempfile import TemporaryDirectory

__this_file = path.realpath(__file__)
__this_dir = path.dirname(__this_file)
__test_dir = path.join(__this_dir, "callgrind")


def _get_test_ids(test_dir):
    test_ids = []
    files = glob(path.join(test_dir, "*.json"))
    for file in files:
        file = path.basename(file)
        if file.startswith("_"):
            continue
        test_id = file[0:-5]
        test_ids.append(test_id)
    return test_ids


def _create_test_class(test_dir):
    class TestCallgrind:
        @staticmethod
        def _load_test(test_id):
            test_file = path.join(TestCallgrind._test_dir, "%s.json" % (test_id,))
            with open(test_file, "r") as f:
                data = json.load(f)
            return data

        @staticmethod
        def _load_result(test_id):
            test_file = path.join(
                TestCallgrind._test_dir, "_%s.callgrind.json" % (test_id,)
            )
            with open(test_file, "r") as f:
                data = json.load(f)
            return data

        @staticmethod
        def _gen_result(test_id):
            data = TestCallgrind._load_test(test_id)
            if not path.isabs(data["binary_name"]):
                files = glob("build/**/%s" % (data["binary_name"],), recursive=True)
                assert len(files) == 1
                data["binary_name"] = path.abspath(files[0])
            with TemporaryDirectory() as tmp:
                cmd = [
                    "valgrind",
                    "--tool=callgrind",
                    "--show-below-main=yes",
                    "--callgrind-out-file=callgrind.out",
                ]
                env = {
                    "LD_BIND_NOW": "1",
                }
                if "function_name" in data and data["function_name"] != "":
                    cmd.append("--toggle-collect=%s" % (data["function_name"],))
                cmd.append("%s" % (data["binary_name"],))
                if "args" in data:
                    cmd = cmd + data["args"]
                check_output(cmd, cwd=tmp, env=env)
                result = callgrind_parser.parse(
                    fileinput.input(files=path.join(tmp, "callgrind.out"))
                )
                total = 0
                for key, val in result.items():
                    total += val
                result[" total"] = total
            return result

        @staticmethod
        def _save_result(test_id):
            result = json.dumps(TestCallgrind._gen_result(test_id), indent=2, sort_keys=True)
            output_file = path.join(
                TestCallgrind._test_dir, "_%s.callgrind.json" % (test_id,)
            )
            with open(output_file, "w") as f:
                f.write(result)

        @staticmethod
        def _run_test(test_id):
            expected_result = TestCallgrind._load_result(test_id)
            current_result = TestCallgrind._gen_result(test_id)
            assert expected_result == current_result

    setattr(TestCallgrind, "_test_dir", test_dir)

    test_ids = _get_test_ids(test_dir)
    for test_id in test_ids:

        def test_func(self, test_id=test_id):
            TestCallgrind._run_test(test_id)

        setattr(TestCallgrind, "test_%s" % (test_id,), test_func)

    return TestCallgrind


TestCallgrind = _create_test_class(__test_dir)


def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=("generate",))
    args = parser.parse_args()
    if args.cmd == "generate":
        test_ids = _get_test_ids(__test_dir)
        for test_id in test_ids:
            TestCallgrind._save_result(test_id)


if __name__ == "__main__":
    main()
