# MIT License
# 
# Copyright (c) 2023 Can Joshua Lehmann
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import std/[math, sets, tables, sequtils, strutils, sugar, options]

type
  NodeKind = enum
    NodeConst, NodeVar
    NodeAdd, NodeMul,
    NodeNegate, NodeReciprocal,
    NodePow, NodeMod,
    NodeSin, NodeCos, NodeTan,
    NodeFloor, NodeCeil, NodeAbs,
    NodeMax, NodeMin,
    NodeLn
  
  Node* = ref object
    children: seq[Node]
    case kind: NodeKind:
      of NodeConst: value: int
      of NodeVar: name: string
      else: discard

const
  NaryNodes = {
    NodeAdd, NodeMul,
    NodeMax, NodeMin
  }
  UnaryNodes = {
    NodeNegate, NodeReciprocal,
    NodeSin, NodeCos, NodeTan,
    NodeFloor, NodeCeil, NodeAbs,
    NodeLn
  }
  BinaryNodes = {
    NodePow, NodeMod
  }

proc findVariables(node: Node): HashSet[string] =
  case node.kind:
    of NodeVar: result = toHashSet([node.name])
    else:
      for child in node.children:
        result = result.union(child.findVariables())

proc eval*[T](node: Node, vars: Table[string, T]): T =
  case node.kind:
    of NodeConst: T(node.value)
    of NodeVar:
      case node.name:
        of "pi": T(PI) # TODO: Find a better system for constants
        of "e": T(E)
        else:
          if node.name notin vars:
            raise newException(ValueError, "Variable undefined")
          vars[node.name]
    of NaryNodes:
      let children = node.children.map(child => child.eval(vars))
      case node.kind:
        of NodeAdd: sum(children)
        of NodeMul: prod(children)
        of NodeMax: max(children)
        of NodeMin: min(children)
        else:
          raise newException(ValueError, "Unreachable")
    of UnaryNodes:
      let value = node.children[0].eval(vars)
      case node.kind:
        of NodeNegate: -value
        of NodeReciprocal: T(1) / value
        of NodeSin: sin(value)
        of NodeCos: cos(value)
        of NodeTan: tan(value)
        of NodeFloor: floor(value)
        of NodeCeil: ceil(value)
        of NodeAbs: abs(value)
        of NodeLn: ln(value)
        else:
          raise newException(ValueError, "Unreachable")
    of BinaryNodes:
      let
        a = node.children[0].eval(vars)
        b = node.children[1].eval(vars)
      case node.kind:
        of NodePow: pow(a, b)
        of NodeMod: a mod b
        else:
          raise newException(ValueError, "Unreachable")

proc stringify(node: Node, level: int): string =
  const LEVELS = [
    NodeConst: 10,
    NodeVar: 10,
    NodeAdd: 2,
    NodeMul: 3,
    NodeNegate: 4,
    NodeReciprocal: 5,
    NodePow: 6,
    NodeMod: 3
  ]
  
  const FUNCTION_NAMES = [
    NodeSin: "sin",
    NodeCos: "cos",
    NodeTan: "tan",
    NodeFloor: "floor",
    NodeCeil: "ceil",
    NodeAbs: "abs",
    NodeMax: "max",
    NodeMin: "min",
    NodeLn: "ln"
  ]
  
  let terms = node.children.map(child => child.stringify(LEVELS[node.kind] + 1))
  result = case node.kind:
    of NodeConst: $node.value
    of NodeVar: node.name
    of NodeAdd: terms.join(" + ")
    of NodeMul: terms.join(" * ")
    of NodeNegate: "-" & terms[0]
    of NodeReciprocal: "1/" & terms[0]
    of NodePow: terms[0] & " ^ " & terms[1]
    of NodeMod: terms[0] & " % " & terms[1]
    else:
      FUNCTION_NAMES[node.kind] & "(" & terms.join(",") & ")"
  
  if LEVELS[node.kind] < level:
    result = "(" & result & ")"

proc `$`*(node: Node): string = node.stringify(0)

proc new*(_: typedesc[Node], kind: NodeKind, children: varargs[Node]): Node =
  result = Node(kind: kind, children: @children)

proc constant*(_: typedesc[Node], value: int): Node =
  result = Node(kind: NodeConst, value: value)

proc `-`*(a: Node): Node = Node.new(NodeNegate, a)

proc `+`*(a, b: Node): Node = Node.new(NodeAdd, a, b)
proc `-`*(a, b: Node): Node = Node.new(NodeAdd, a, -b)
proc `*`*(a, b: Node): Node = Node.new(NodeMul, a, b)
proc `/`*(a, b: Node): Node = Node.new(NodeMul, a, Node.new(NodeReciprocal, b))
proc `^`*(a, b: Node): Node = Node.new(NodePow, a, b)
proc `mod`*(a, b: Node): Node = Node.new(NodeMod, a, b)

proc x(_: typedesc[Node]): Node = Node(kind: NodeVar, name: "x")

# Parser

proc parse*(source: string): Node =
  # Tokenization
  
  type
    TokenKind = enum
      TokenInt, TokenFractional, TokenName,
      TokenOp, TokenPrefixOp,
      TokenParOpen, TokenParClose,
      TokenComma, TokenSemicolon
    
    Token = object
      kind: TokenKind
      value: string
  
  proc tokenize(source: string): seq[Token] =
    const
      OP_CHARS = {'+', '-', '*', '/', '^', '%'}
      WHITESPACE = {' ', '\n', '\t', '\r'}
      SINGLE_CHAR_TOKENS = {'(', ')', ',', ';'}
    
    var it = 0
    
    proc readDigits(): string =
      while it < source.len and (source[it] in '0'..'9' or source[it] == '_'):
        result.add(source[it])
        it += 1
    
    while it < source.len:
      case source[it]:
        of WHITESPACE:
          it += 1
        of '(':
          result.add(Token(kind: TokenParOpen))
          it += 1
        of ')':
          result.add(Token(kind: TokenParClose))
          it += 1
        of ',':
          result.add(Token(kind: TokenComma))
          it += 1
        of ';':
          result.add(Token(kind: TokenSemicolon))
          it += 1
        of OP_CHARS:
          let isPrefix = (it > 0 and source[it - 1] in WHITESPACE + {'(', ',', ';'} or it == 0) and
                         it + 1 < source.len and source[it + 1] notin WHITESPACE
          
          var op = ""
          while it < source.len and source[it] in OP_CHARS:
            op.add(source[it])
            it += 1
          
          if isPrefix:
            result.add(Token(kind: TokenPrefixOp, value: op))
          else:
            result.add(Token(kind: TokenOp, value: op))
        of '0'..'9':
          result.add(Token(kind: TokenInt, value: readDigits()))
          if it < source.len and source[it] == '.':
            it += 1
            let frac = readDigits()
            if frac.len > 0:
              result.add(Token(kind: TokenFractional, value: frac))
        else:
          var name = ""
          while it < source.len and
                source[it] notin OP_CHARS + WHITESPACE + SINGLE_CHAR_TOKENS:
            name.add(source[it])
            it += 1
          result.add(Token(kind: TokenName, value: name))
  
  # Parsing Utilities
  
  type TokenStream = object
    tokens: seq[Token]
    cur: int
  
  proc next(stream: TokenStream, kind: TokenKind): bool =
    result = stream.cur < stream.tokens.len and
             stream.tokens[stream.cur].kind == kind
  
  proc take(stream: var TokenStream, kind: TokenKind): bool =
    result = stream.next(kind)
    if result:
      stream.cur += 1
  
  proc value(stream: TokenStream): string =
    result = stream.tokens[stream.cur - 1].value
  
  # Grammar
  
  proc parse(stream: var TokenStream, level: int, allowPrefix: bool = true): Node
  
  proc parseArguments(stream: var TokenStream): Option[seq[Node]] =
    if not stream.take(TokenParOpen):
      return none(seq[Node])
    
    var args: seq[Node] = @[]
    while true:
      let arg = stream.parse(0)
      if arg.isNil:
        break
      args.add(arg)
      if not stream.take(TokenComma):
        break
    
    if not stream.take(TokenParClose):
      return none(seq[Node])
    
    return some(args)
  
  proc parse(stream: var TokenStream, level: int, allowPrefix: bool = true): Node =
    if stream.take(TokenInt):
      result = Node.constant(stream.value.parseInt())
      if stream.take(TokenFractional):
        let
          num = Node.constant(stream.value.parseInt())
          den = Node.constant(10 ^ stream.value.len)
        result = result + num / den
    elif stream.take(TokenName):
      let name = stream.value
      var isFunction = true
      case name:
        of "sin": result = Node(kind: NodeSin)
        of "cos": result = Node(kind: NodeCos)
        of "tan": result = Node(kind: NodeTan)
        of "floor": result = Node(kind: NodeFloor)
        of "ceil": result = Node(kind: NodeCeil)
        of "abs": result = Node(kind: NodeAbs)
        of "max": result = Node(kind: NodeMax)
        of "min": result = Node(kind: NodeMin)
        of "sqrt", "cbrt":
          isFunction = false
          let args = stream.parseArguments()
          if args.isNone or args.get().len != 1:
            return nil
          let nth = if name == "sqrt": 2 else: 3
          result = Node.new(NodePow,
            args.get()[0],
            Node.new(NodeReciprocal, Node.constant(nth))
          )
        of "ln": result = Node(kind: NodeLn)
        else:
          result = Node(kind: NodeVar, name: name)
          isFunction = false
      
      if isFunction:
        let args = stream.parseArguments()
        if args.isNone:
          return nil
        result.children = args.get()
    elif stream.take(TokenParOpen):
      result = stream.parse(0)
      if result.isNil or not stream.take(TokenParClose):
        return nil
    elif allowPrefix and stream.take(TokenPrefixOp):
      result = case stream.value:
        of "+": stream.parse(4)
        of "-":
          let arg = stream.parse(4)
          if arg.isNil:
            return nil
          else:
            -arg
        else:
          return nil
    
    if result.isNil:
      return nil
    
    # Parse operators after value
    const MUL_LEVEL = 3
    while stream.next(TokenOp) or level <= MUL_LEVEL:
      if stream.take(TokenOp):
        let 
          op = stream.value
          opLevel = case op:
            of "+": 2
            of "-": 2
            of "*": MUL_LEVEL
            of "/": MUL_LEVEL
            of "^": 4
            of "%": MUL_LEVEL
            else: return nil
        
        if opLevel < level:
          stream.cur -= 1
          return
        
        let other = stream.parse(opLevel + 1)
        if other.isNil:
          return nil
        
        result = case op:
          of "+": result + other
          of "-": result - other
          of "*": result * other
          of "/": result / other
          of "^": result ^ other
          of "%": result mod other
          else: return nil
      else:
        let other = stream.parse(MUL_LEVEL + 1, allowPrefix = false)
        if other.isNil:
          return
        result = Node.new(NodeMul, result, other)
  
  # Tokenize and parse given expression
  
  let tokens = tokenize(source)
  var stream = TokenStream(tokens: tokens)
  result = stream.parse(0)
  if stream.cur < stream.tokens.len:
    result = nil

# Tests

when isMainModule:
  proc equals(a: Node,
              b: proc(x: float): float,
              domain: HSlice[float, float] = -10.0..10.0,
              steps: int = 10,
              eps: float = 0.0001): bool =
    for it in 0..<steps:
      let
        x = domain.a + (domain.b - domain.a) * (it / (steps - 1))
        valueA = a.eval(toTable({"x": x}))
        valueB = b(x)
      if abs(valueA - valueB) > eps:
        return false
    return true
  
  proc equals(a, b: Node,
              domain: HSlice[float, float] = -10.0..10.0,
              steps: int = 10,
              eps: float = 0.0001): bool =
    result = equals(a, x => b.eval(toTable({"x": x})),
      domain = domain,
      steps = steps,
      eps = eps
    )
  
  proc equals(a: Node,
              b: float,
              eps: float = 0.0001): bool =
    result = equals(a, x => b,
      domain = 0.0..0.0,
      steps = 1,
      eps = eps
    )
  
  
  # Tests / Operator Precedence
  
  assert equals(parse("2 * 3 + 1"), 7)
  assert equals(parse("1 + 2 * 3"), 7)
  assert equals(parse("(1 + 2) * 3"), 9)
  assert equals(parse("2 * (3 + 1)"), 8)
  
  assert equals(parse("2 3 + 1"), 7)
  assert equals(parse("1 + 2 3"), 7)
  assert equals(parse("(1 + 2)3"), 9)
  assert equals(parse("2(3 + 1)"), 8)
  
  assert equals(parse("1/2(3+4)"), 3.5)
  assert equals(parse("1 + 2 * 4 - 3 * 4"), -3)
  
  # Tests / Pow
  
  assert equals(parse("2^4"), 16)
  assert equals(parse("x^2"), parse("x * x"))
  assert equals(parse("x^3"), parse("x * x * x"))
  assert equals(parse("e^x"), x => exp(x))
  
  # Tests / Mod
  
  assert equals(parse("6 % 4"), 2)
  assert equals(parse("-6 % 4"), -2)
  
  # Tests / Sin
  
  assert equals(parse("sin(x)"), sin)
  assert equals(parse("sin(0)"), 0)
  assert equals(parse("sin(pi / 2)"), 1)
  assert equals(parse("sin(pi)"), 0)
  assert equals(parse("sin(3/2 pi)"), -1)
  assert equals(parse("sin(2pi)"), 0)
  assert equals(parse("sin(2pi + x)"), parse("sin(x)"))
  
  # Tests / Cos
  
  assert equals(parse("cos(x)"), cos)
  assert equals(parse("cos(0)"), 1)
  assert equals(parse("cos(pi / 2)"), 0)
  assert equals(parse("cos(pi)"), -1)
  assert equals(parse("cos(3/2 pi)"), 0)
  assert equals(parse("cos(2pi)"), 1)
  assert equals(parse("cos(2pi + x)"), parse("cos(x)"))
  
  # Tests / Tan
  
  assert equals(parse("tan(x)"), tan)
  
  # Tests / Floor
  
  assert equals(parse("floor(x)"), floor)
  assert equals(parse("floor(1.2)"), 1)
  assert equals(parse("floor(1.0)"), 1)
  assert equals(parse("floor(0.8)"), 0)
  assert equals(parse("floor(0)"), 0)
  assert equals(parse("floor(-1.2)"), -2)
  
  # Tests / Ceil
  
  assert equals(parse("ceil(x)"), ceil)
  assert equals(parse("ceil(1.2)"), 2)
  assert equals(parse("ceil(1.0)"), 1)
  assert equals(parse("ceil(0.8)"), 1)
  assert equals(parse("ceil(0)"), 0)
  assert equals(parse("ceil(-1.2)"), -1)
  
  # Tests / Abs
  
  assert equals(parse("abs(x)"), x => abs(x))
  assert equals(parse("abs(10)"), 10)
  assert equals(parse("abs(-10)"), 10)
  
  # Tests / Max
  
  assert equals(parse("max(0, x)"), x => max(0, x))
  assert equals(parse("max(1, 2)"), 2)
  assert equals(parse("max(-x, x)"), parse("abs(x)"))
  assert equals(parse("max(1)"), 1)
  assert equals(parse("max(1, 3, 2)"), 3)
  
  # Tests / Min
  
  assert equals(parse("min(0, x)"), x => min(0, x))
  assert equals(parse("min(1, 2)"), 1)
  assert equals(parse("min(-x, x)"), parse("-abs(x)"))
  assert equals(parse("min(1)"), 1)
  assert equals(parse("min(1, 3, -2)"), -2)
  
  # Tests / Ln
  
  assert equals(parse("ln(x)"), ln, domain=0.1..10.0)
  assert equals(parse("ln(1)"), 0)
  assert equals(parse("ln(e)"), 1)
  assert equals(parse("ln(e ^ 2)"), 2)
  assert equals(parse("e^ln(x)"), x => x, domain=0.1..10.0)
  assert equals(parse("ln(x^2)"), parse("2 ln(x)"), domain=0.1..10.0)
  
  # Tests / Polynomial
  
  assert equals(parse("5x^2 - x + 1"), x => 5 * x^2 - x + 1)
  assert equals(parse("-5x^2 x + 3x - 2"), x => -5 * x^3 + 3 * x - 2)
  assert equals(parse("(x + 1)(x - 1)"), x => x^2 - 1)
  assert equals(parse("(x + 2)(x - 3)^2"), x => (x + 2) * (x - 3)^2)
