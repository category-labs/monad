from behave import given  # type: ignore
import tempfile
import subprocess
import os


@given("I run tdb with the output")
def given_run_tdb(context):
    with tempfile.NamedTemporaryFile() as tp:
        tp.write(context.output)
        tp.flush()
        # TODO: Issue #113
        result = subprocess.run(
            ["python3", os.getcwd() + "/monad/tdb/tdb.py", "--log", tp.name],
            capture_output=True,
            text=True,
        )
        context.output = result.stdout


@given("I run tdb with the output and account {account}")
def given_run_tdb_with_account(context, account):
    with tempfile.NamedTemporaryFile() as tp:
        tp.write(context.output)
        tp.flush()
        # TODO: Issue #113
        result = subprocess.run(
            [
                "python3",
                os.getcwd() + "/monad/tdb/tdb.py",
                "--log",
                tp.name,
                "--account",
                account,
            ],
            capture_output=True,
            text=True,
        )
        context.output = result.stdout
