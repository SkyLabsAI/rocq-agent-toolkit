from rocq_doc_manager import RocqDocManager

def main():
    try:
        dm = RocqDocManager([], "test.v")
        print(dm.request("non-existant", []))
        print(dm.request("load_file", []))
        print(dm.request("doc_suffix", []))
        dm.quit()
    except RocqDocManager.Error as e:
        print(e)

if __name__ == '__main__':
    main()
