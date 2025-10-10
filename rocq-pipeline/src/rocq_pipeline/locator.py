"""
Locators scan Rocq documents leave the cursor at the given task.
"""
import re
from typing import override
from rocq_doc_manager import RocqDocManager

# Auxiliary functions, possibly better to put on RDM directly?
def scan_to(rdm: RocqDocManager, fn):
    """
    Scans a document until it reaches a command where `fn` returns `True`.
    The identified command is *not* evaluated.
    """
    suffix = rdm.doc_suffix()
    for cmd in suffix:
        if cmd['kind'] == 'command' and fn(cmd['text']):
            return True
        rdm.run_step()
    return False

# The interface
class NotFound(Exception):
    """Exception raised if the locator failed to find its target"""
    pass

class Locator:
    """
    We use a locator class so that we can provide `__str__()`
    """
    def __call__(self, rdm: RocqDocManager) -> bool:
        return False

class FirstAdmit(Locator):
    """Find the first `admit` in the file."""
    @override
    def __call__(self, rdm: RocqDocManager):
        def is_admit(tac: str):
            return tac.startswith('admit')
        return scan_to(rdm, is_admit)

class FirstLemma(Locator):
    """
    Find the first lemma with the given name.
    """
    _name: str
    _style: str | None

    def __init__(self, lemma_name: str, style: str | None = None):
        """
        If style is `None`, then we look for any definition that
        opens a proof. Otherwise, we use it as the type of lemma,
        e.g. `Lemma`, `Theorem`, `Example`.
        """
        self._name = lemma_name
        self._style = style

    @override
    def __call__(self, rdm: RocqDocManager) -> bool:
        if self._style is None:
            prefix = 'Lemma|Theorem'
        else:
            prefix = self._style

        mtch = re.compile(f'({prefix})\\s+{self._name}[^0-9a-zA-Z_]')
        def is_lemma(cmd: str):
            return mtch.match(cmd)

        if scan_to(rdm, is_lemma):
            rdm.run_step() # advance past the lemma statement
            for cmd in rdm.doc_suffix():
                if cmd['kind'] == 'blank' or \
                   (cmd['kind'] == 'command' and cmd['text'].startswith('Proof')):
                    rdm.run_step()
                else:
                    return True

        print("failed to find lemma")
        return False

def parse_locator(s:str) -> Locator:
    if s.startswith('lemma:'):
        return FirstLemma(s[len('lemma:'):])
    if s == 'admit':
        return FirstAdmit()
    return Locator()
