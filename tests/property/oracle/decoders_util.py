"""Hexadecimal words of the oracle protocol."""


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def tohex(data):
    data = bytes(data)
    return data.hex() if data else "-"
