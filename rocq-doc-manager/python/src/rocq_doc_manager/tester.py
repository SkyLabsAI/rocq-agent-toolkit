import sys

from rocq_doc_manager import RocqDocManager


def cram_test1() -> None:
    try:
        dm = RocqDocManager([], sys.argv[1])
        print(dm.raw_request("non-existant", []))
        print(dm.raw_request("load_file", []))
        print(dm.raw_request("doc_suffix", []))
        dm.quit()
    except RocqDocManager.Error as e:
        print(e)
