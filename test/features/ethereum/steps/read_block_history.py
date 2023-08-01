import os
import re
import subprocess
from behave import given, when, then

from util.util import log_mapping, logger_and_level_to_output


@given('I run with BlockDb path = "{block_db_path}"')
def given_block_db_path(context, block_db_path):
    context.block_db_path = block_db_path


@given('I run with StateDb path = "{state_db_path}"')
def given_block_db_path(context, state_db_path):
    context.state_db_path = state_db_path
    dir_path = os.getcwd() + "/test/features/ethereum/" + state_db_path
    if os.path.exists(dir_path):
        subprocess.run(["rm", "-rf", dir_path])
    subprocess.run(["mkdir", dir_path])


@given('I run with inferred start block number = "{start_block_number}"')
def given_start_block_number(context, start_block_number):
    if start_block_number == 0:
        pass
    state_db_path = os.getcwd() + "/test/features/ethereum/" + context.state_db_path
    result = subprocess.run(
        [
            "mkdir",
            "-p",
            state_db_path + "/" + str(int(start_block_number) - 1) + "/rockstriedb",
        ]
    )


@given('I run with finish block number = "{finish_block_number}"')
def given_finish_block_number(context, finish_block_number):
    context.finish_block_number = finish_block_number


@given('I run with "{logger_name}" log level = "{log_level}"')
def given_log_level(context, logger_name, log_level):
    setattr(context, f"{logger_name}_level", str(log_mapping[log_level]))


@given("I run with default log level")
def step_impl(context):
    # Default log level = 4, so we don't need to do anything
    pass


@when('I start "{program}"')
def when_start(context, program):
    executable_path = os.getcwd() + "/build/src/monad/execution/ethereum/" + program
    if not hasattr(context, "block_db_path"):
        raise ValueError("Block Db path is required")
    if not hasattr(context, "state_db_path"):
        raise ValueError("State Db path is required")
    args = [
        executable_path,
        "--block_db",
        os.getcwd() + "/../../" + context.block_db_path,
        "--state_db",
        os.getcwd() + "/test/features/ethereum/" + context.state_db_path,
    ]
    if hasattr(context, "finish_block_number"):
        args += ["--finish", context.finish_block_number]
    args += ["log_levels"]
    if hasattr(context, "main_logger_level"):
        args += ["--main", context.main_logger_level]
    if hasattr(context, "block_logger_level"):
        args += ["--block", context.block_logger_level]
    if hasattr(context, "txn_logger_level"):
        args += ["--txn", context.txn_logger_level]
    if hasattr(context, "state_logger_level"):
        args += ["--state", context.state_logger_level]
    if hasattr(context, "trie_db_logger_level"):
        args += ["--trie_db", context.trie_db_logger_level]
    result = subprocess.run(args, capture_output=True, text=True)
    context.output = result.stdout
    context.returncode = result.returncode


@then('the output should contain "{number}" "{value}"')
def then_output_contain_with_number(context, number, value):
    assert context.returncode == 0
    assert context.output.count(value) == int(number)


@then('the output should not contain "{value}"')
def then_output_contain_with_number(context, value):
    assert value not in context.output


@then('the output should contain "{logger_name}" "{log_level}" log')
def then_output_contain(context, logger_name, log_level):
    assert context.returncode == 0
    assert (logger_name, log_level) in logger_and_level_to_output
    value = logger_and_level_to_output[(logger_name, log_level)]
    assert value in context.output


@then('the output should not contain "{logger_name}" "{log_level}" log')
def then_output_no_contain(context, logger_name, log_level):
    assert context.returncode == 0
    assert (logger_name, log_level) in logger_and_level_to_output
    value = logger_and_level_to_output[(logger_name, log_level)]
    assert value not in context.output


@then("the output should be empty")
def then_output_empty(context):
    assert context.returncode == 0
    assert context.output == ""


@then('the "{root_type}" should match')
def then_root_match(context, root_type):
    lines = context.output.splitlines()

    assert context.returncode == 0

    for line in lines:
        if root_type in line:
            match = re.search(
                r"Computed (\w+) Root: (\w+), Expected (\w+) Root: (\w+)", line
            )
            assert match.group(2) == match.group(4)
