import asyncio
import sys

from rocq_doc_manager import create

from . import rocq_doc_manager_api as rdm_api


async def acram_test1() -> None:
    try:
        async with (await create(sys.argv[1], rocq_args=[])).sess() as dm:
            rc = dm.cursor()
            # print(dm.raw_request("non-existant", []))
            print(await rc.load_file())
            print(await rc.doc_suffix())
            await rc.dispose()
    except rdm_api.Error as e:
        print(e)


def cram_test1() -> None:
    asyncio.run(acram_test1())
