import sys

from rocq_doc_manager import create, RocqCursor


def cram_test1() -> None:
    try:
        with create([], sys.argv[1]).sess() as dm:
            rc = dm.cursor()
            # print(dm.raw_request("non-existant", []))
            print(rc.load_file())
            print(rc.doc_suffix())
            rc.dispose()
    except RocqCursor.Error as e:
        print(e)
