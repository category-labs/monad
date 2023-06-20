from behave import given  # type: ignore
import subprocess
import os


@given("I run db unit test {unit_test}")
def given_run_unit_test(context, unit_test):
    result = subprocess.run(
        [
            #  TODO: make cmake configure this file path, or provide
            #  that on the command line. This is issue #113
            os.getcwd() + "/build/src/monad/db/test/monad-dbtests",
            f"--gtest_filter={unit_test}",
        ],
        capture_output=True,
    )
    context.output = result.stdout
