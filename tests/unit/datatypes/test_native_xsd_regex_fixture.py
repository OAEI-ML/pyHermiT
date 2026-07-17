from tools.datatypes.build_xsd_regex_fixture import DEFAULT_OUTPUT as FIXTURE
from tools.datatypes.build_xsd_regex_fixture import render as render_fixture
from tools.datatypes.build_xsd_unicode_table import DEFAULT_OUTPUT as UNICODE_TABLE
from tools.datatypes.build_xsd_unicode_table import render as render_unicode_table


def test_native_xsd_regex_fixture_is_canonical_and_reproducible() -> None:
    assert FIXTURE.read_text(encoding="utf-8") == render_fixture()


def test_native_xsd_unicode_table_is_canonical_and_reproducible() -> None:
    assert UNICODE_TABLE.read_text(encoding="utf-8") == render_unicode_table()
