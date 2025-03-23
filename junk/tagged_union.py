#!/usr/bin/env python3

import typing

import rich


class Base:
    ty: str


class DerA(Base):
    ty: typing.Literal["DerA"]


class DerB(Base):
    ty: typing.Literal["DerA"]


rich.inspect(Base, all=True)
rich.inspect(DerA, all=True)
rich.inspect(DerB, all=True)

rich.inspect(Base(), all=True)
rich.inspect(DerA(), all=True)
rich.inspect(DerB(), all=True)
