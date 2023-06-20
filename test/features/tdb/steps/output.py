from behave import then  # type: ignore


@then('the output should contain "{value}"')
def then_output_contain(context, value):
    print(value, context.output)
    assert value in context.output
