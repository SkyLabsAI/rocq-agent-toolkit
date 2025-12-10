import sys

import rocq_doc_manager
from rocq_doc_manager import RocqDocManagerAPI


def cram_test1() -> None:
    try:
        with rocq_doc_manager.create([], sys.argv[1]).sess() as dm:
            rc = dm.cursor()
            # print(dm.raw_request("non-existant", []))
            print(rc.load_file())
            print(rc.doc_suffix())
            rc.dispose()
    except RocqDocManagerAPI.Error as e:
        print(e)
