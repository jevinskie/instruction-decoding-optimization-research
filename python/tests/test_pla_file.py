import instdec.pla_file as pla_file


def test_pla_file_load():
    po = pla_file.PLA([], 0, 0)
    assert po is not None
