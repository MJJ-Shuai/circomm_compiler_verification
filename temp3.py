import math


class MontMul:
    """docstring for ClassName"""
    def __init__(self, R, N):
        self.N = N
        self.R = R
        self.logR = int(math.log(R, 2))
        N_inv = MontMul.modinv(N, R)
        self.N_inv_neg = R - N_inv
        self.R2 = (R*R)%N

    @staticmethod
    def egcd(a, b):
        if a == 0:
            return (b, 0, 1)
        else:
            g, y, x = MontMul.egcd(b % a, a)
            return (g, x - (b // a) * y, y)

    @staticmethod
    def modinv(a, m):
        g, x, y = MontMul.egcd(a, m)
        if g != 1:
            raise Exception('modular inverse does not exist')
        else:
            return x % m

    def REDC(self, T):
        N, R, logR, N_inv_neg = self.N, self.R, self.logR, self.N_inv_neg

        m = ((T&int('1'*logR, 2)) * N_inv_neg)&int('1'*logR, 2) # m = (T%R * N_inv_neg)%R
        t = (T+m*N) >> logR # t = int((T+m*N)/R)
        if t >= N:
            return t-N
        else:
            return t

    def ModMul(self, a, b):
        if a >= self.N or b >= self.N:
            raise Exception('input integer must be smaller than the modulus N')

        R2 = self.R2
        aR = self.REDC(a*R2) # convert a to Montgomery form
        bR = self.REDC(b*R2) # convert b to Montgomery form
        T = aR*bR # standard multiplication
        abR = self.REDC(T) # Montgomery reduction
        return self.REDC(abR) # covnert abR to normal ab


if __name__ == '__main__':
    N = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
    R = 2**256 # assume here we are working on 64-bit integer multiplication
    g, x, y = MontMul.egcd(N, R)
    if R <= N or g != 1:
        raise Exception('N must be larger than R and gcd(N,R) == 1')

    # 1 的蒙哥马利数
    m1 = 6350874878119819312338956282401532410528162663560392320966563075034087161851

    inst = MontMul(R, N)
    R_ = inst.REDC(1)
    print((R * R_) % N)

    print(hex(m1))