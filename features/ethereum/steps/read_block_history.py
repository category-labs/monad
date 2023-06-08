import os
import re
import subprocess
from behave import given, when, then


@given('I run replay_ethereum_block_db with BlockDb path = "{block_db_path}"')
def given_block_db_path(context, block_db_path):
    context.block_db_path = block_db_path


@given(
    'I run replay_ethereum_block_db with start block number = "{start_block_number}"'
)
def given_start_block_number(context, start_block_number):
    context.start_block_number = start_block_number


@given(
    'I run replay_ethereum_block_db with finish block number = "{finish_block_number}"'
)
def given_finish_block_number(context, finish_block_number):
    context.finish_block_number = finish_block_number


@given('I run replay_ethereum_block_db with log level = "{log_level}"')
def given_log_level(context, log_level):
    context.log_level = log_level


@when('I start "{program}"')
def when_start(context, program):
    executable_path = os.getcwd() + "/build/src/monad/execution/ethereum/" + program
    if not hasattr(context, "block_db_path"):
        raise ValueError("Block Db path is required")
    if not hasattr(context, "start_block_number"):
        raise ValueError("Start block number is required")
    args = [
        executable_path,
        "--block-db",
        os.getcwd() + "/../../" + context.block_db_path,
        "--start",
        context.start_block_number,
    ]
    if hasattr(context, "finish_block_number"):
        args += ["--finish", context.finish_block_number]
    if hasattr(context, "log_level"):
        args += ["--log-level", context.log_level]
    result = subprocess.run(args, capture_output=True, text=True)
    context.output = result.stdout


@then('the output should contain "{number}" "{value}"')
def then_output_contain(context, number, value):
    assert context.output.count(value) == int(number)


@then("the output should not contain any block level information")
def then_output_empty(context):
    assert "block_logger" not in context.output


@then('the "{root_type}" should match')
def then_root_match(context, root_type):
    lines = context.output.splitlines()

    for line in lines:
        if root_type in line:
            hashes = re.findall(r"\[([^\]]*)\]", line)
            assert hashes[1] == hashes[2]
