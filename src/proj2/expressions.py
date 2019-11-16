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
        return "({} {} {})".format(self.name, self.left.render(), self.right.render())


class UnaryExpression:
    def __init__(self, expr):
        self.expr = expr
        self.name = ""

    def render(self):
        return "({} {})".format(self.name, self.expr.render())


class And(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "and"


class Or(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "or"


class Implies(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "=>"


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


class B2i(UnaryExpression):
    definition = "(define-fun b2i ((b Bool)) Int (ite b 1 0))"

    def __init__(self, expr):
        super().__init__(expr)
        self.name = "b2i"
