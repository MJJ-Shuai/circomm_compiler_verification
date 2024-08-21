from paramiko.util import bit_length

from Tools.ValueDeal import reverse_pairs

if __name__ == '__main__':
    i = 1
    target = 0x0216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7
    q = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
    while True:
        R = 2 ** i
        R2 = R * R
        mod = R2 % q
        if mod == target:
            break
        i += 1

    print(f'end! i == {i}')

    test = q - 1

    # 1 的蒙哥马利数
    R_mod_q = 6350874878119819312338956282401532410528162663560392320966563075034087161851
    print(f'R       == {hex(R_mod_q)}')
    print(f'length  == {bit_length(R_mod_q)}')

    outcome = R_mod_q * test
    print(f'outcome == {hex(outcome)}')
    print(f'length  == {bit_length(outcome)}')

    length_lim = 2**256
    cut = outcome % length_lim
    print(f'cut     == {hex(outcome%length_lim)}')
    print(f'cut % q == {hex(cut%q)}')
    print(f'out % q == {hex(outcome%q)}')

    mong = reverse_pairs('06 00 00 A0 77 C1 4B 97 67 A3 58 DA B2 71 37 F1 2E 12 08 09 47 A2 E1 51 FA C0 29 47 B1 D6 59 22')
    print(f'circom  == {hex(mong)}')

    print(hex((2**256 * -1)%q))
