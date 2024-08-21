from Elements.Circuit.BuildinWords import EIO, EPO


def calculate_deterministic_infixOp(left, op, right, prime):
    if op == EIO.Add.value:
        return (left + right) % prime
    elif op == EIO.Sub.value:
        return (left - right) % prime
    elif op == EIO.Mul.value:
        return (left * right) % prime
    elif op == EIO.Div.value:
        return (left / right) % prime
    elif op == EIO.Lesser.value:
        return val(left, prime) < val(right, prime)
    elif op == EIO.LesserEq.value:
        return val(left, prime) <= val(right, prime)
    elif op == EIO.Greater.value:
        return val(left, prime) > val(right, prime)
    elif op == EIO.GreaterEq.value:
        return val(left, prime) >= val(right, prime)
    elif op == EIO.Eq.value:
        return val(left, prime) == val(right, prime)
    elif op == EIO.NotEq.value:
        return val(left, prime) != val(right, prime)


def calculate_deterministic_prefixOp(op, right, prime):
    if op == EPO.Sub.value:
        return (-right) % prime


def val(raw, prime):
    if prime + 2 <= raw * 2 <= prime * 2:
        return raw - prime
    else:
        return raw
