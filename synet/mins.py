import z3


def max2(t1, t2):
    """
    Get the maximum of list of two numerical t1 and t2
    Caution: it will return t1 if the variables are equal
    """
    return z3.If(t1 >= t2, t1, t2)


def get_max(*args):
    """
    Get the maximum of list of numerical variables
    Caution: it will return the first in the list if there multiple equally MAXs
    """
    assert len(args) >= 2
    if len(args) == 2:
        return max2(*args)
    else:
        return max2(args[0], get_max(*args[1:]))


def min2(t1, t2):
    """
    Get the minimum of list of two numerical t1 and t2
    Caution: it will return t1 if the variables are equal
    """
    return z3.If(t1 <= t2, t1, t2)


def get_min(*args):
    """
    Get the minimum of list of numerical variables
    Caution: it will return the first in the list if there multiple equally MAXs
    """
    if len(args) == 2:
        return min2(*args)
    else:
        return min2(args[0], get_max(*args[1:]))


def min2_eval(eval_func, t1, t2):
    """Returns the t1 or t2 based if eval_func(t1) <= eval_func(t2)"""
    return z3.If(eval_func(t1) <= eval_func(t2), t1, t2)


def min2_eval_select(select_func, select_val, eval_func, none_value, t1, t2):
    """
    This is a bit more complicated min function with lots of nobs!
    if select_func(t1) == select_val && select_func(t1) == select_val, then act a min2_eval
    if one of t1 or t2 select_val(tx) == select_val then return it
    if none of t1 and t2 mathes the input then return the none_value
    """
    return z3.If(
        z3.And(select_func(t1) == select_val, select_func(t2) == select_val),
        min2_eval(eval_func, t1, t2),
        z3.If(
            select_func(t1) == select_val,
            t1,
            z3.If(select_func(t2) == select_val,
                  t2,
                  none_value
                  )
        ))


def get_min_eval_select(select_func, select_val, eval_func, none_value, *args):
    """See min2_eval_select"""
    assert len(args) >= 2
    if len(args) == 2:
        return min2_eval_select(select_func, select_val, eval_func, none_value, *args)
    else:
        return min2_eval_select(select_func, select_val, eval_func, none_value, args[0],
                                get_min_eval_select(select_func, select_val, eval_func ,none_value, *args[1:]))


