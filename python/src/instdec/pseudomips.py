import enum
from typing import Final

# https://github.com/jevinskie/mips--/blob/master/project4/source/common.vhd

OpBits: Final[int] = 6


class PMIPSOpcode(enum.IntEnum):
    special = 0b000000
    regimm = 0b000001
    j = 0b000010
    jal = 0b000011
    beq = 0b000100
    bne = 0b000101
    blez = 0b000110
    bgtz = 0b000111
    addi = 0b001000
    addiu = 0b001001
    slti = 0b001010
    sltiu = 0b001011
    andi = 0b001100
    ori = 0b001101
    xori = 0b001110
    lui = 0b001111
    cop0 = 0b010000
    cop1 = 0b010001
    cop2 = 0b010010
    cop1x = 0b010011
    beql = 0b010100
    bnel = 0b010101
    blezl = 0b010110
    bgtzl = 0b010111
    special2 = 0b011100
    jalx = 0b011101
    special3 = 0b011111
    lb = 0b100000
    lh = 0b100001
    lwl = 0b100010
    lw = 0b100011
    lbu = 0b100100
    lhu = 0b100101
    lwr = 0b100110
    sb = 0b101000
    sh = 0b101001
    swl = 0b101010
    sw = 0b101011
    swr = 0b101110
    cache = 0b101111
    ll = 0b110000
    lwc1 = 0b110001
    lwc2 = 0b110010
    pref = 0b110011
    ldc1 = 0b110101
    ldc2 = 0b110110
    sc = 0b111000
    swc1 = 0b111001
    swc2 = 0b111010
    sdc1 = 0b111101
    sdc2 = 0b111110
    halt = 0b111111


class PMIPSSFunc(enum.IntEnum):
    sll = 0b000000
    movci = 0b000001
    srl = 0b000010
    sra = 0b000011
    sllv = 0b000100
    srlv = 0b000110
    srav = 0b000111
    jr = 0b001000
    jalr = 0b001001
    movz = 0b001010
    movn = 0b001011
    syscall = 0b001100
    breakf = 0b001101
    sync = 0b001111
    mfhi = 0b010000
    mthi = 0b010001
    mflo = 0b010010
    mtlo = 0b010011
    mult = 0b011000
    multu = 0b011001
    div = 0b011010
    divu = 0b011011
    add = 0b100000
    addu = 0b100001
    sub = 0b100010
    subu = 0b100011
    andf = 0b100100
    orf = 0b100101
    xor = 0b100110
    nor = 0b100111
    slt = 0b101010
    sltu = 0b101011
    tge = 0b110000
    tgeu = 0b110001
    tlt = 0b110010
    tltu = 0b110011
    teq = 0b110100
    tne = 0b110110
