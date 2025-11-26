import itertools
from collections.abc import Callable


def merge_dict[K,V](d1: dict[K,V], d2: dict[K,V], merge:Callable[[K,V,V],V]|None=None) -> dict[K,V]:
    """
    Merge two dictionaries using hte `merge` function to handle overlapping values.
    """
    for k , v in d2.items():
        if k in d1:
            if d1[k] == v:
                continue
            d1[k] = merge(k, d1[k], v) if merge else v
        else:
            d1[k] = v
    return d1

def extend_args(rocq_args: list[str], ext: list[str]) -> list[str]:
    """
    Extend the Rocq command line arguments `rocq_args` with new arguments.

    An error is thrown if there is an incompatibility
    """
    q:dict[str,tuple[str, bool]] = {}
    i:list[str] = []
    extra:list[str] = []
    j = 0
    all_args = rocq_args + ext
    while j < len(all_args):
        if all_args[j] == '-I':
            i.append(all_args[j+1])
            j = j + 2
        elif all_args[j] == '-Q':
            q[all_args[j+2]] = (all_args[j+1], False)
            j = j + 3
        elif all_args[j] == '-R':
            q[all_args[j+2]] = (all_args[j+1], True)
            j = j + 3
        else:
            extra.append(all_args[j])
            j = j + 1
    return extra + list(itertools.chain.from_iterable([["-I",p] for p in i])) + list(itertools.chain.from_iterable([["-R" if r else "-Q", p, mp] for mp, (p,r) in q.items()]))
