# -*- coding: utf-8 -*-
"""
Author: Peng Lingwei
Date: 2024-11-27
License: MIT
"""


class Expr:
    pass


class Level:
    def __init__(self, level: int | str) -> None:
        self.level = level

    def __repr__(self) -> str:
        return f"{self.level}"

    def __eq__(self, value: object) -> bool:
        if isinstance(value, Level):
            return self.level == self.level
        return False


class MaxLevel(Level):
    def __init__(self, left: Level, right: Level) -> None:
        if isinstance(left.level, int) and isinstance(right.level, int):
            self.level = max(left.level, right.level)
        elif isinstance(left.level, int):
            self.level = f"(max {right.level} {left.level})"
        elif isinstance(right.level, int):
            self.level = f"(max {left.level} {right.level})"
        elif left.level > right.level:
            self.level = f"(max {right.level} {left.level})"
        else:
            self.level = f"(max {left.level} {right.level})"


class SuccLevel(Level):
    def __init__(self, level: Level) -> None:
        if isinstance(level.level, int):
            self.level = level.level + 1
        self.level = f"{level.level}+1"


# 在 Lean4 里 Sort 0 = Prop, Sort 1 = Type 0, Sort 2 = Type 1
class Sort(Expr):
    def __init__(self, level: Level | int | str):
        if isinstance(level, Level):
            self.level: Level = level
        else:
            self.level: Level = Level(level)

    def __repr__(self) -> str:
        return f"(Sort {self.level})"


class Type(Expr):
    def __init__(self, level: Level | int | str) -> None:
        if isinstance(level, Level):
            self.level: Level = level
        else:
            self.level: Level = Level(level)

    def __repr__(self):
        if isinstance(self.level.level, int) and self.level.level == 0:
            return "Type"
        return f"(Type {self.level})"


class Const(Expr):
    def __init__(self, name: str, type_expr: Expr = None):
        self.name = name
        self.type = type_expr

    def __repr__(self):
        return f"{self.name}"


class BoundVar(Expr):
    def __init__(self, index: int):
        self.index = index

    def __repr__(self):
        return f"#{self.index}"


class Forall(Expr):
    def __init__(self, var_name: str, var_type: Expr, body: Expr):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body

    def __repr__(self) -> str:
        return f"(Forall ({self.var_name} : {self.var_type}) {self.body})"


class Lambda(Expr):
    def __init__(self, var_name: str, var_type: Expr, body: Expr):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body

    def __repr__(self) -> str:
        return f"(Lambda ({self.var_name} : {self.var_type}) {self.body})"


class App(Expr):
    def __init__(self, func: Expr, arg: Expr):
        self.func = func
        self.arg = arg

    def __repr__(self) -> str:
        return f"(App {self.func} {self.arg})"

class Proj(Expr):
    def __init__(self, tuple_expr: Expr, index: int):
        self.tuple_expr = tuple_expr
        self.index = index

    def __repr__(self):
        return f"(Proj {self.tuple_expr} {self.index})"


VarType = tuple[Expr, Expr]


def shift_context(context: list[VarType]):
    new_context = []
    for expr, type in context:
        shifted_expr = shift_expr(expr)
        shifted_type = shift_expr(type)
        new_context.append((shifted_expr, shifted_type))
    return new_context


def shift_expr(expr: Expr, offset=0):
    if isinstance(expr, BoundVar):
        if expr.index >= offset:
            return BoundVar(expr.index + 1)
        return expr
    elif isinstance(expr, Const):
        shifted_type = shift_expr(expr.type, offset=offset)
        return Const(expr.name, shifted_type)
    elif isinstance(expr, Lambda):
        shifted_var_type = shift_expr(expr.var_type, offset=offset)
        shifted_body = shift_expr(expr.body, offset=offset + 1)
        return Lambda(expr.var_name, shifted_var_type, shifted_body)
    elif isinstance(expr, Forall):
        shifted_var_type = shift_expr(expr.var_type, offset=offset)
        shifted_body = shift_expr(expr.body, offset=offset + 1)
        return Forall(expr.var_name, shifted_var_type, shifted_body)
    elif isinstance(expr, App):
        shifted_func = shift_expr(expr.func, offset=offset)
        shifted_arg = shift_expr(expr.arg, offset=offset)
        return App(shifted_func, shifted_arg)
    return expr


def unshift_expr(expr: Expr, offset=0, head=None):
    if isinstance(expr, BoundVar):
        if expr.index >= offset:
            if expr.index == offset:
                return head
            return BoundVar(expr.index - 1)
        return expr
    elif isinstance(expr, Const):
        shifted_type = unshift_expr(expr.type, offset=offset, head=head)
        return Const(expr.name, shifted_type)
    elif isinstance(expr, Lambda):
        shifted_var_type = unshift_expr(expr.var_type, offset=offset, head=head)
        shifted_body = unshift_expr(expr.body, offset=offset + 1, head=shift_expr(head))
        return Lambda(expr.var_name, shifted_var_type, shifted_body)
    elif isinstance(expr, Forall):
        shifted_var_type = unshift_expr(expr.var_type, offset=offset, head=head)
        shifted_body = unshift_expr(expr.body, offset=offset + 1, head=shift_expr(head))
        return Forall(expr.var_name, shifted_var_type, shifted_body)
    elif isinstance(expr, App):
        shifted_func = unshift_expr(expr.func, offset=offset, head=head)
        shifted_arg = unshift_expr(expr.arg, offset=offset, head=head)
        return App(shifted_func, shifted_arg)
    return expr


def get_level(expr: Expr, context: list[tuple[Expr, Expr]] = None) -> Level:
    if context is None:
        context = []
    if isinstance(expr, Sort):
        return expr.level
    elif isinstance(expr, Type):
        return SuccLevel(expr.level)
    elif isinstance(expr, Forall):
        left = get_level(expr.var_type, context)
        right = get_level(
            expr.body, [(BoundVar(0), expr.var_type)] + shift_context(context)
        )
        return MaxLevel(left, right)
    elif isinstance(expr, BoundVar):
        next_expr, next_expr_type = context[expr.index]
        if isinstance(next_expr, BoundVar):
            next_expr.index == expr.index
            return Level(-1)
        return get_level(next_expr, context)
    return Level(-1)


# 用于比较Type，所以不会有Lambda和Proj这两个节点。
def eq(expr1: Expr, expr2: Expr, context: list[Expr] = None) -> bool:
    if context is None:
        context = []
    if isinstance(expr1, BoundVar):
        if expr1.index < len(context):
            target = context[expr1.index]
            if not isinstance(target, BoundVar) or expr1.index != target.index:
                # 排除自己指向自己
                return eq(target, expr2, context)
        elif isinstance(expr2, BoundVar):
            if expr2.index < len(context):
                target = context[expr2.index]
                if not isinstance(target, BoundVar) or expr2.index != target.index:
                    # 排除自己指向自己
                    return eq(expr1, target, context)
        return str(expr1) == str(expr2)
    elif isinstance(expr2, BoundVar):
        if expr2.index < len(context):
            target = context[expr2.index]
            if not isinstance(target, BoundVar) or expr2.index != target.index:
                # 排除自己指向自己
                return eq(expr1, target, context)
        return str(expr1) == str(expr2)
    elif isinstance(expr1, Const) and expr1.type is None and expr1.name in type_pool:
        return eq(type_pool[expr1.name], expr2, context)
    elif isinstance(expr2, Const) and expr2.type is None and expr2.name in type_pool:
        return eq(expr1, type_pool[expr2.name], context)
    elif isinstance(expr1, Const):
        if (
            isinstance(expr2, Const)
            and expr1.name == expr2.name
            and eq(expr1.type, expr2.type, context)
        ):
            return True
        elif (
            isinstance(expr2, Sort)
            and isinstance(expr2.level.level, int)
            and expr2.level.level == 0
        ):
            # Sort 0 == Prop
            return eq(expr1, type_pool["Prop"])
        return False
    elif isinstance(expr1, Lambda):
        if isinstance(expr2, Lambda) and eq(expr1.var_type, expr2.var_type, context):
            if eq(
                expr1.body,
                expr2.body,
                [Const(expr1.var_name, shift_expr(expr1.var_type))]
                + [shift_expr(e) for e in context],
            ):
                return True
        return False
    elif isinstance(expr1, Forall):
        if (isinstance(expr2, Forall)) and eq(expr1.var_type, expr2.var_type, context):
            if eq(
                expr1.body,
                expr2.body,
                context=[Const(expr1.var_name, shift_expr(expr1.var_type))]
                + [shift_expr(e) for e in context],
            ):
                return True
        return False
    elif isinstance(expr1, App):
        if (
            isinstance(expr2, App)
            and eq(expr1.arg, expr2.arg, context)
            and eq(expr1.func, expr2.func, context)
        ):
            return True
        return False
    elif isinstance(expr1, Type):
        if isinstance(expr2, Type):
            return expr1.level == expr2.level
        elif isinstance(expr2, Sort):
            # Type u = Sort u + 1
            return SuccLevel(expr1.level) == expr2.level
    elif isinstance(expr1, Sort):
        if isinstance(expr1.level.level, int) and expr1.level.level == 0:
            # Sort 0 == Prop
            return eq(type_pool["Prop"], expr2)
        elif isinstance(expr2, Sort):
            return expr1.level == expr2.level
        elif isinstance(expr2, Type):
            # Type u = Sort u + 1
            return expr1.level == SuccLevel(expr2.level)
    return False


def type_check(type1: Expr, type2: Expr) -> bool:
    return eq(type1, type2)


def calc(expr: Expr, context: list[VarType] = None) -> tuple[Expr, Expr]:
    if context is None:
        context = []
    if isinstance(expr, BoundVar):
        assert expr.index < len(
            context
        ), f"Index {expr.index} out of bounds for context: {context}"
        return context[expr.index]
    elif isinstance(expr, Const):
        if expr.type is None and expr.name in type_pool:
            expr = type_pool[expr.name]
            return_expr, return_expr_type = calc(expr, context)
            return return_expr, return_expr_type
        expr_type, _ = calc(expr.type, context)
        return (expr, expr_type)
    elif isinstance(expr, Lambda):
        var_type, _ = calc(expr.var_type, context)
        shifted_context = shift_context(context)
        shifted_var_type = shift_expr(var_type)
        shifted_body, shifted_body_type = calc(
            expr.body, [(BoundVar(0), shifted_var_type)] + shifted_context
        )
        return_expr = Lambda(expr.var_name, var_type, shifted_body)
        return_type = Forall(expr.var_name, var_type, shifted_body_type)
        return return_expr, return_type
    elif isinstance(expr, Forall):
        var_type, _ = calc(expr.var_type, context)
        shifted_context = shift_context(context)
        shifted_var_type = shift_expr(var_type)
        shifted_body, shifted_body_type = calc(
            expr.body, [(BoundVar(0), shifted_var_type)] + shifted_context
        )
        return_expr = Forall(expr.var_name, var_type, shifted_body)
        level = get_level(return_expr, context)
        if isinstance(level.level, int) and level.level == -1:
            return_type = Prop
        else:
            return_type = Type(level)
        return return_expr, return_type
    elif isinstance(expr, App):
        arg, arg_type = calc(expr.arg, context)
        func, func_type = calc(expr.func, context)
        assert isinstance(func_type, Forall)
        assert type_check(
            func_type.var_type, arg_type
        ), f"Type mismatch: want {func_type.var_type}, get {arg_type} \n  {expr}"
        unshifted_funcbody_type = unshift_expr(func_type.body, head=arg)
        if isinstance(func, Lambda):
            unshifted_funcbody = unshift_expr(func.body, head=arg)
            return unshifted_funcbody, unshifted_funcbody_type
        return App(func, arg), unshifted_funcbody_type
    elif isinstance(expr, Type):
        return expr, Type(SuccLevel(expr.level))
    elif isinstance(expr, Sort):
        if isinstance(expr.level.level, int):
            if expr.level.level == 0:
                return Prop, Prop.type
            else:
                return Type(Level(expr.level.level - 1)), Type(expr.level)
        return expr, Type(expr.level)
    elif isinstance(expr, Proj):
        tuple_value, tuple_type = calc(expr.tuple_expr, context)
        # 确保 tuple_type 是一个 Forall 表示元组类型
        assert isinstance(tuple_type, Forall), f"Type of tuple {tuple_value} is not valid: {tuple_type}"
        # 获取元组对应的第 index 个类型
        current_type = tuple_type
        for _ in range(expr.index):
            assert isinstance(current_type.body, Forall), f"Invalid tuple type at index {expr.index}: {current_type}"
            current_type = current_type.body
        return Proj(tuple_value, expr.index), current_type.var_type
    else:
        raise ValueError("Unknown expr", expr)


Prop = Const("Prop", Type(0))
Decidable = Const("Decidable", Forall("a", Prop, Type(0)))
type_pool = {
    "Prop": Const("Prop", Type(0)),
    "Decidable": Const("Decidable", Forall("a", Prop, Type(0))),
    "Not": Const("Not", Forall("a", Prop, Prop)),
    "Iff": Const("Iff", Forall("a", Prop, Forall("b", Prop, Prop))),
    "Iff_intro": Const(
        "Iff_intro",
        Forall(
            "a",
            Prop,
            Forall(
                "b",
                Prop,
                Forall(
                    "mp",
                    Forall("c", BoundVar(1), BoundVar(1)),
                    Forall(
                        "mpr",
                        Forall("d", BoundVar(1), BoundVar(3)),
                        App(App(Const("Iff"), BoundVar(3)), BoundVar(2)),
                    ),
                ),
            ),
        ),
    ),
}

Eq = Forall(
    "p",
    Sort(0),
    Forall(
        "h1",
        Forall("a", BoundVar(0), BoundVar(1)),
        Forall("h2", BoundVar(1), BoundVar(2)),
    ),
)
Eq_proof = Lambda(
    "p",
    Sort(0),
    Lambda(
        "h1",
        Forall("a", BoundVar(0), BoundVar(1)),
        Lambda("h2", BoundVar(1), App(BoundVar(1), BoundVar(0))),
    ),
)
print("Eq:\n ", Eq)
print("Eq_proof:\n ", Eq_proof)
Eq_proof_calc, Eq_proof_calc_type = calc(Eq_proof)
print("Eq_proof_calc:\n ", Eq_proof_calc)
print("Eq_proof_calc_type:\n ", Eq_proof_calc_type)
print("Check proof of eq_proof_calc:\n ", eq(Eq, Eq_proof_calc_type))

Iff_refl = Forall("a", Sort(0), App(App(Const("Iff"), BoundVar(0)), BoundVar(0)))
# 定义证明值
Iff_refl_proof = Lambda(
    "a",
    Prop,
    App(
        App(
            App(App(Const("Iff_intro"), BoundVar(0)), BoundVar(0)),
            Lambda("h", BoundVar(0), BoundVar(0)),
        ),
        Lambda("h", BoundVar(0), BoundVar(0)),
    ),
)

print("Iff_intro:\n ", type_pool["Iff_intro"])

print("Iff_refl:\n ", Iff_refl)
print("Iff_refl_proof:\n ", Iff_refl_proof)

Iff_refl_proof_calc, Iff_refl_proof_calc_type = calc(Iff_refl_proof)
print("Iff_refl_proof_calc:\n ", Iff_refl_proof_calc)
print("Iff_refl_proof_calc_type:\n ", Iff_refl_proof_calc_type)
print("Check proof:\n ", eq(Iff_refl, Iff_refl_proof_calc_type))

# Decidable 类型相关表达式
type_pool["Decidable.isTrue"] = Const("Decidable.isTrue", Forall(
    "p", Sort(0), Forall("h", BoundVar(0), App(Const("Decidable"), BoundVar(1)))
))

type_pool["Decidable.isFalse"] = Const("Decidable.isFalse", Forall(
    "p",
    Sort(0),
    Forall("h", App(Const("Not"), BoundVar(0)), App(Const("Decidable"), BoundVar(1))),
))

type_pool["Decidable.rec"] = Const("Decidable.rec", Forall(
    "p",
    Sort(0),
    Forall(
        "motive",
        Forall(
            "t",
            App(Const("Decidable"), BoundVar(0)),
            Sort("u"),
        ),
        Forall(
            "isFalse",
            Forall(
                "h",
                App(Const("Not"), BoundVar(1)),
                App(
                    BoundVar(1),
                    App(
                        App(Const("Decidable.isFalse"), BoundVar(2)),
                        BoundVar(0),
                    ),
                ),
            ),
            Forall(
                "isTrue",
                Forall(
                    "h",
                    BoundVar(2),
                    App(
                        BoundVar(2),
                        App(
                            App(Const("Decidable.isTrue"), BoundVar(3)),
                            BoundVar(0),
                        ),
                    ),
                ),
                Forall(
                    "t",
                    App(Const("Decidable"), BoundVar(3)),
                    App(BoundVar(3), BoundVar(0)),
                ),
            ),
        ),
    ),
))

type_pool["Decidable.casesOn"] = Const("Decidable.casesOn", Forall(
    "p",
    Sort(0),
    Forall(
        "motive",
        Forall(
            "t",
            App(Const("Decidable"), BoundVar(0)),
            Sort("u"),
        ),
        Forall(
            "t",
            App(Const("Decidable"), BoundVar(1)),
            Forall(
                "isFalse",
                Forall(
                    "h",
                    App(Const("Not"), BoundVar(2)),
                    App(
                        BoundVar(2),
                        App(
                            App(Const("Decidable.isFalse"), BoundVar(3)),
                            BoundVar(0),
                        ),
                    ),
                ),
                Forall(
                    "isTrue",
                    Forall(
                        "h",
                        BoundVar(3),
                        App(
                            BoundVar(3),
                            App(
                                App(Const("Decidable.isTrue"), BoundVar(4)),
                                BoundVar(0),
                            ),
                        ),
                    ),
                    App(BoundVar(3), BoundVar(2)),
                ),
            ),
        ),
    ),
))

Decidable_casesOn_proof = Lambda(
    "p",
    Sort(0),
    Lambda(
        "motive",
        Forall(
            "t",
            App(Const("Decidable"), BoundVar(0)),
            Sort("u"),
        ),
        Lambda(
            "t",
            App(Const("Decidable"), BoundVar(1)),
            Lambda(
                "isFalse",
                Forall(
                    "h",
                    App(Const("Not"), BoundVar(2)),
                    App(
                        BoundVar(2),
                        App(
                            App(Const("Decidable.isFalse"), BoundVar(3)),
                            BoundVar(0),
                        ),
                    ),
                ),
                Lambda(
                    "isTrue",
                    Forall(
                        "h",
                        BoundVar(3),
                        App(
                            BoundVar(3),
                            App(
                                App(Const("Decidable.isTrue"), BoundVar(4)),
                                BoundVar(0),
                            ),
                        ),
                    ),
                    App(
                        App(
                            App(
                                App(
                                    App(Const("Decidable.rec"), BoundVar(4)),
                                    BoundVar(3),
                                ),
                                Lambda(
                                    "h",
                                    App(Const("Not"), BoundVar(4)),
                                    App(BoundVar(2), BoundVar(0)),
                                ),
                            ),
                            Lambda(
                                "h",
                                BoundVar(4),
                                App(BoundVar(1), BoundVar(0)),
                            ),
                        ),
                        BoundVar(2),
                    ),
                ),
            ),
        ),
    ),
)

# 验证 Decidable.casesOn 类型
casesOn = type_pool["Decidable.casesOn"]
print(casesOn, ":\n ", casesOn.type)
print("casesOn_proof:\n ", Decidable_casesOn_proof)
casesOn_proof_calc, casesOn_proof_calc_type = calc(Decidable_casesOn_proof)
print("casesOn_proof_calc:\n ", casesOn_proof_calc)
print("casesOn_proof_calc_type:\n ", casesOn_proof_calc_type)
print("Check proof:\n ", eq(casesOn.type, casesOn_proof_calc_type))
