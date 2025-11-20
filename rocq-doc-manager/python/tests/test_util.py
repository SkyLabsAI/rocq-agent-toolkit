from rocq_doc_manager import RocqDocManager

from .util import RDM_Tests


class Test_RDM_Tests(RDM_Tests):
    @staticmethod
    def test_fixtures_ok(
            transient_shared_rdm: RocqDocManager,
            transient_rdm: RocqDocManager,
            loadable_rdm: RocqDocManager
    ) -> None:
        assert not isinstance(
            transient_shared_rdm.cursor_index(),
            RocqDocManager.Err,
        )
        assert not isinstance(
            transient_rdm.cursor_index(),
            RocqDocManager.Err,
        )
        with loadable_rdm.sess() as rdm:
            assert not isinstance(
                rdm.cursor_index(),
                RocqDocManager.Err,
            )

    @classmethod
    def test_constants_ok(cls) -> None:
        for nm, val in cls.CONSTANTS().items():
            assert val is not None, f"{cls.__name__}.{nm} is None"
