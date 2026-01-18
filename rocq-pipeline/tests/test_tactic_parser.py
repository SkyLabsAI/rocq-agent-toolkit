import pytest

# Import the function we want to test
from rocq_pipeline.taggers import tactic_tagger

# Define the map of inputs (keys) to expected outputs (values)
# This dictionary represents the test cases: {input_string: expected_list}
TEST_CASES: dict[str, list[str]] = {
    # Basic cases
    "idtac": ["idtac"],
    "foo; bar": ["foo", "bar"],
    "foo; [ bar | baz |]": ["foo", "bar", "baz"],
    "go; [ a | b ] => /rw": ["go", "a", "b"],
    "go; first [ a | b ]": ["go", "a", "b"],
    "go; try solve [ a | b ]": ["go", "a", "b"],
    "assert (x)by b": ["assert (x)", "b"],
    "assert(x) by b": ["assert(x)", "b"],
    "assert (x) by (a;b)": ["assert (x)", "a", "b"],
    # Edge cases
    "": [],
    " ": [],  # Empty string after stripping whitespace
    ";": [],  # Only delimiters
    "  ; ; ": [],
    "- rewrite x": ["rewrite x"],
    "-": [],
    "*": [],
    "+": [],
    "2:{ ": [],
    "last rewrite H": ["rewrite H"],
    "1: rewrite h": ["rewrite h"],
    "vc_split=>?": ["vc_split=>?"],
    "do 5 rewrite H": ["rewrite H"],
    "do 15 rewrite H": ["rewrite H"],
}

# 1. Get the list of input strings (keys) for the test ID/name
INPUTS = list(TEST_CASES.keys())


# 2. Use pytest.mark.parametrize to run the test function once for each item
@pytest.mark.parametrize(
    "input_string, expected_output", TEST_CASES.items(), ids=INPUTS
)
def test_parse_with_map(input_string: str, expected_output: list[str]) -> None:
    """
    Tests the parse function using all cases defined in the TEST_CASES map.
    """
    # Call the function with the input string
    actual_output = tactic_tagger.flatten_tactic_string(input_string)

    # Assert that the actual result matches the expected result
    assert actual_output == expected_output, (
        f"Input: '{input_string}' | Expected: {expected_output} | Got: {actual_output}"
    )
