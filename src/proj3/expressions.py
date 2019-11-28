class Literal:
    literals = set()

    def __init__(self, name):
        self.name = name
        Literal.literals.add(name)

    def render(self):
        return self.name

    @staticmethod
    def clean():
        Literal.literals = set()


class Int:
    def __init__(self, value):
        self.value = value

    def render(self):
        return str(self.value)


class BinaryExpression:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.name = ""

    def render(self):
        return "({} {} {})".format(self.left.render(), self.name, self.right.render())


class UnaryExpression:
    def __init__(self, expr):
        self.expr = expr
        self.name = ""

    def render(self):
        return "({} {})".format(self.name, self.expr.render())


class And(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "/\\"


class Or(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "\\/"


class Implies(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "->"


class Iff(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "<->"


class Sum(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "+"


class Equals(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "="


class Not(UnaryExpression):
    def __init__(self, expr):
        super().__init__(expr)
        self.name = "not"


class B2i:
    definition = "function var int: b2i(var bool: b) = if b then 1 else 0 endif;"

    def __init__(self, expr):
        self.expr = expr

    def render(self):
        return "b2i({})".format(self.expr.render())
