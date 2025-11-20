import pytest

# Import the function we want to test
from rocq_pipeline import task_manip

# Define the map of inputs (keys) to expected outputs (values)
# This dictionary represents the test cases: {input_string: expected_list}
TEST_CASES: list[tuple[tuple[list[str],list[str],list[str]], bool]] = [
    ((["a"], [], []), True),
    (([], [], []), True),
    ((["a"], ["a"], []), True),
    ((["a"], ["a"], []), True),
    ((["a"], [], ["a"]), False),
    ((["a"], ["a"], ["a"]), False),
    ((["a"], ["a|b"], []), True),
    ((["b"], ["a|b"], []), True),
    (([], ["a|b"], []), False),
]

# 1. Get the list of input strings (keys) for the test ID/name
INPUTS = [str(x) for x,_ in TEST_CASES]

# 2. Use pytest.mark.parametrize to run the test function once for each item
@pytest.mark.parametrize("input, expected_output",
                         TEST_CASES,
                         ids=INPUTS)
def test_eval_options(input : tuple[list[str],list[str],list[str]], expected_output: bool) -> None:
    """
    Tests the parse function using all cases defined in the TEST_CASES map.
    """
    (tags, with_tags, without_tags) = input
    # Call the function with the input string
    actual_output = task_manip.eval_options(tags, with_tags, without_tags)

    # Assert that the actual result matches the expected result
    assert actual_output == expected_output, \
        f"Input: '{input}' | Expected: {expected_output} | Got: {actual_output}"
