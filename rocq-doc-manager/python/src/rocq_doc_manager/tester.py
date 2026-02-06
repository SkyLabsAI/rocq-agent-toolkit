import sys

from rocq_doc_manager import create

from . import rocq_doc_manager_api as rdm_api


def cram_test1() -> None:
    try:
        with create([], sys.argv[1]).sess() as dm:
            rc = dm.cursor()
            # print(dm.raw_request("non-existant", []))
            print(rc.load_file())
            print(rc.doc_suffix())
            rc.dispose()
    except rdm_api.Error as e:
        print(e)
