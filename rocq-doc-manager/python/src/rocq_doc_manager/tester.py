import sys

from rocq_doc_manager import RocqDocManager


def cram_test1() -> None:
    try:
        dm = RocqDocManager([], sys.argv[1])
        print(dm.request("non-existant", []))
        print(dm.request("load_file", []))
        print(dm.request("doc_suffix", []))
        dm.quit()
    except RocqDocManager.Error as e:
        print(e)
