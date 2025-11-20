import re


def split_at_top_level(text: str, separator: str) -> list[str]:
    """
    Splits a string by a separator, but only at the top level
    (i.e., not inside parentheses or brackets).
    """

    def _is_word_char(char: str) -> bool:
        """
        Defines what constitutes a character INSIDE a tactic name.
        If a character is NOT in this set, it is a boundary (separator).
        """
        return char.isalnum() or char in '_-'

    parts = []
    balance_paren = 0
    balance_bracket = 0
    current_part_start = 0
    sep_len = len(separator)
    text_len = len(text)
    i = 0

    # We treat the separator as a "word" (requiring boundaries) only if
    # it is composed purely of letters (like 'by').
    # Symbols like ';' or '|' do not require boundary checks.
    is_word_separator = separator.isalpha()

    while i < text_len:
        char = text[i]

        # 1. Track Balance
        if char == '(':
            balance_paren += 1
        elif char == ')':
            balance_paren = max(0, balance_paren - 1)
        elif char == '[':
            balance_bracket += 1
        elif char == ']':
            balance_bracket = max(0, balance_bracket - 1)

        # 2. Check for Separator at Top Level
        # We check if the substring starting at 'i' matches the separator
        if (balance_paren == 0 and balance_bracket == 0 and
            text[i:i+sep_len] == separator):

            is_valid_split = True

            if is_word_separator:
                # A word separator must NOT be adjacent to other word chars.

                # Check char strictly BEFORE the separator
                # If i=0, it's a valid boundary (start of string)
                if i > 0 and _is_word_char(text[i-1]):
                    is_valid_split = False

                # Check char strictly AFTER the separator
                # If end_idx=len, it's a valid boundary (end of string)
                end_idx = i + sep_len
                if end_idx < text_len and _is_word_char(text[end_idx]):
                    is_valid_split = False

            if is_valid_split:
                parts.append(text[current_part_start:i])
                current_part_start = i + sep_len
                # Skip past the separator
                i += sep_len - 1

        i += 1

    parts.append(text[current_part_start:])
    return parts

def get_atomic_tactics(chunk: str) -> list[str]:
    """
    Recursively parses a Rocq tactic and returns a flat list
    of all base tactics found within it.
    """

    # Clean chunk
    chunk = chunk.strip().strip(';.').strip()

    if not chunk:
        return []

    #1. Descend into the 'wrappers' try / first / solve
    WRAPPER_PATTERN = re.compile(r"^(try|first|solve)(\s+|(?=[\[\(]))")
    match = WRAPPER_PATTERN.match(chunk)
    if match:
        content = chunk[match.end():].strip()
        if content.startswith('(') and content.endswith(')'):
            content = content[1:-1].strip()
        return get_atomic_tactics(content)

    #2. Handle [ X1 | X2 | ... Xn ]
    if chunk.startswith('['):
        each = split_at_top_level(chunk[1:], ']')
        content = each[0]
        # TODO: currently ignore each[1:]

        # Only split if we actually find the separator |
        parts = split_at_top_level(content, '|')
        if len(parts) > 1:
            results = []
            for part in parts:
                results.extend(get_atomic_tactics(part))
            return results

    #3. Handle X1; X2; ... Xn
    parts = split_at_top_level(chunk, ';')
    if len(parts) > 1:
        results = []
        for part in parts:
            results.extend(get_atomic_tactics(part))
        return results

    #4. Check 'by' keyword
    parts = split_at_top_level(chunk, 'by')
    if len(parts) > 1:
        results = []
        for idx, part in enumerate(parts):
            part = part.strip()
            # If this part is the RHS of a 'by' (index > 0), unwrap parens
            # e.g. "assert X by (lia)" -> split -> "assert X", "(lia)" -> unwrap -> "lia"
            if idx > 0 and part.startswith('(') and part.endswith(')'):
                part = part[1:-1]
            results.extend(get_atomic_tactics(part))
        return results

    # Base Case: a single tactic is returned as a singleton list.
    return [chunk]

def flatten_tactic_string(s: str) -> list[str]:
    """
    Flattens a nested tactic string into a flat list of individual tactics.

    Handles:
    - 'by ...' (Proof terminator)
    - 'try', 'first', 'solve' wrappers
    - ';' and '|' separators
    - 'tactic by script' separators (merged logic)
    """

    s_to_process = s.strip()

    # Handle Proof Terminator 'by ...'
    if s_to_process.startswith('by ') and s_to_process.endswith('.'):
        content = s_to_process[3:-1].strip()
        s_to_process = content[1:-1].strip() if (content.startswith('(') and content.endswith(')')) else content
    elif s_to_process.startswith('by(') and s_to_process.endswith('.'):
        content = s_to_process[2:-1].strip()
        s_to_process = content[1:-1].strip() if (content.startswith('(') and content.endswith(')')) else content

    return get_atomic_tactics(s_to_process)

def filter_tactics(tactics: list[str], prefixes: list[str]) -> tuple[list[str], list[str]]:
    """
    Filters a list of tactics based on a given set of prefixes

    Args:
        chunks: The input list of strings; chunks are allready 'stripped'
                so do not contain leading or trailing whitespaces
        prefixes: A list of allowwed tactic prefixes

    Returns:
        A tuple containing two lists, both sorted and without duplicates:
        1. identified_tactics: A list of unique tactic prefixes found.
        2. leftovers: A list of unique processed chunks that did not match.
    """

    # Use sets to store results to automatically handle duplicates
    identified_tactics_set = set()
    leftovers_set = set()

    for tac in tactics:
        found_prefix = None

        for prefix in prefixes:
            # Construct regex:
            # ^             : Start of string
            # {escaped}     : The prefix (escaped for safety)
            # (?= ... )     : Lookahead for boundary
            #    [\s.(]     : Whitespace, dot, or open parenthesis
            #    |          : OR
            #    $          : End of string
            pattern = fr"^{re.escape(prefix)}(?=[\s.(]|$)"

            if re.match(pattern, tac):
                found_prefix = prefix
                break

        if found_prefix:
            identified_tactics_set.add(found_prefix)
        else:
            leftovers_set.add(tac)

    # Convert sets to sorted lists for the final output
    return sorted(identified_tactics_set), sorted(leftovers_set)

rocq_prefixes = ['rewrite', 'erewrite', 'rewrite_all', 'rename',
                 'apply', 'eapply', 'auto', 'eauto', 'auto*', 'eauto*',
                 'assumption', 'eassumption', 'case',
                 'case_decide', 'assert', 'simpl', 'Arith.arith_simpl',
                 'trivial', 'reflexivity', 'cbv', 'cbn', 'subst', 'change',
                 'clear', 'replace', 'specialize', 'generalize',
                 'intro', 'intros', 'destruct', 'inversion', 'exists', 'eexists', 'exfalso',
                 'lia', 'remember', 'symmetry', 'unfold', 'f_equal',
                 'constructor', 'econstructor', 'induction', 'exact', 'elim'
                 'intuition', 'revert', 'split',
                 'left', 'right', 'Opaque', 'Transparent', 'admit',
                 'congruence', 'contradiction', 'discriminate', 'firstorder',
                 'instantiate', 'inversion', 'pose', 'red', 'refine', 'set', 'shelve',
                 'unshelve', 'zify' ]

#from https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md
iris_prefixes = ['iAssert', 'iExists', 'iStartProof', 'iStopProof', 'iExact',
                 'iAssumption', 'iApply', 'iIntros', 'iClear', 'iRevert', 'iRename',
                 'iSpecialize', 'iPoseProof', 'iSelect', 'iPureIntro', 'iLeft', 'iRight',
                 'iSplitL', 'iSplitR', 'iSplit', 'iExFalso', 'iDestruct', 'iFrame',
                 'iCombine', 'iAccu', 'iModIntro', 'iNext', 'iMod', 'iLöb', 'iInduction',
                 'iRewrite', 'iEval', 'iSimpl', 'iUnfold', 'iInv', 'done' ]

brick_prefixes = ['verify_spec', 'go', 'ego', 'work', 'bind_ren', 'ren_hyp',
                  'wp_for', 'wp_while', 'wp_do', 'wp_if' ]

allowed_prefixes = rocq_prefixes + iris_prefixes + brick_prefixes

def extract_tactics(s:str) -> tuple[list[str], list[str]]:
    """
    Flattens a string to a list of tactics and then filters for
    'allowed_prefixes', ensuring no duplicates in the output.

    Args:
        s: The input string containing tactics.

    Returns:
        A tuple containing two lists, both sorted and without duplicates:
        1. identified_tactics: A list of unique tactic prefixes found.
        2. leftovers: A list of unique processed chunks that did not match.
    """

    # Sort prefixes by length (longest first)
    sorted_prefixes = sorted(allowed_prefixes, key=len, reverse=True)

    #flatten the string to a list of tactics
    tactics = flatten_tactic_string(s)

    #filter the tactics by the sorted prefixes and return the result
    return filter_tactics(tactics, sorted_prefixes)
