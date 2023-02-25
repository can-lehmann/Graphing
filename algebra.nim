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
  TypeKind = enum
    TypeNumber, TypeFunction, TypeTuple
  
  Type = ref object
    case kind: TypeKind:
      of TypeNumber: discard
      of TypeFunction:
        args: Option[seq[Type]]
        res: Type
      of TypeTuple:
        fields: Option[seq[Type]]

proc isKind(typ: Type, kind: TypeKind): bool =
  result = not typ.isNil and typ.kind == kind

type
  NodeKind = enum
    NodeConst, NodeVar
    NodeAdd, NodeMul,
    NodeNegate, NodeReciprocal,
    NodePow, NodeMod,
    NodeSin, NodeCos, NodeTan,
    NodeFloor, NodeCeil, NodeAbs,
    NodeMax, NodeMin,
    NodeLn,
    NodeCall
    NodeLambda
    NodeTuple,
    NodeDerive
  
  Node* = ref object
    typeHint: Type
    children: seq[Node]
    case kind: NodeKind:
      of NodeConst: value: int
      of NodeVar: name: string
      of NodeLambda: args: seq[string]
      of NodeDerive: argIndex: int
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

proc new*(_: typedesc[Node], kind: NodeKind, children: varargs[Node]): Node =
  result = Node(kind: kind, children: @children)

proc constant*(_: typedesc[Node], value: int): Node =
  result = Node(
    kind: NodeConst,
    value: value,
    typeHint: Type(kind: TypeNumber)
  )

proc lambda*(_: typedesc[Node], args: seq[string], body: Node): Node =
  result = Node(kind: NodeLambda,
    args: args,
    children: @[body],
    typeHint: Type(
      kind: TypeFunction,
      args: some(newSeq[Type](args.len)),
      res: body.typeHint
    )
  )

proc call*(_: typedesc[Node], callee: Node, args: seq[Node]): Node =
  result = Node(kind: NodeCall, children: @[callee] & args)
  if callee.typeHint.isKind(TypeFunction): # TODO: Error if invalid type or invalid argument types
    result.typeHint = callee.typeHint.res

proc derive*(_: typedesc[Node], function: Node, argIndex: int = 0): Node =
  result = Node(kind: NodeDerive,
    children: @[function],
    argIndex: argIndex,
    typeHint: Type(
      kind: TypeFunction,
      res: Type(kind: TypeNumber)
    )
  )
  if function.typeHint.isKind(TypeFunction):
    # TODO: Check that argIndex < args.len
    result.typeHint.args = function.typeHint.args

{.push inline.}
proc isConst(node: Node): bool = node.kind == NodeConst
proc isConst(node: Node, value: int): bool = node.kind == NodeConst and node.value == value

proc `-`*(a: Node): Node =
  if a.isConst():
    Node.constant(-a.value)
  else:
    Node.new(NodeNegate, a)

proc `+`*(a, b: Node): Node =
  if a.isConst() and b.isConst():
    Node.constant(a.value + b.value)
  elif a.isConst(0):
    b
  elif b.isConst(0):
    a
  else:
    Node.new(NodeAdd, a, b)

proc `-`*(a, b: Node): Node = a + (-b)

proc `*`*(a, b: Node): Node =
  if a.isConst(0) or b.isConst(0):
    Node.constant(0)
  elif a.isConst(1):
    b
  elif b.isConst(1):
    a
  else:
    Node.new(NodeMul, a, b)

proc `/`*(a, b: Node): Node = a * Node.new(NodeReciprocal, b)
proc `^`*(a, b: Node): Node = Node.new(NodePow, a, b)
proc `mod`*(a, b: Node): Node = Node.new(NodeMod, a, b)

proc sin(x: Node): Node = Node.new(NodeSin, x)
proc cos(x: Node): Node = Node.new(NodeCos, x)
proc ln(x: Node): Node = Node.new(NodeLn, x)

proc x(_: typedesc[Node]): Node = Node(kind: NodeVar, name: "x")
{.pop.}

proc findVariables(node: Node): HashSet[string] =
  case node.kind:
    of NodeVar: result = toHashSet([node.name])
    else:
      for child in node.children:
        result = result.union(child.findVariables())

proc derive*(node: Node, varName: string): Node =
  result = case node.kind:
    of NodeConst: Node.constant(0)
    of NodeVar:
      if node.name == varName:
        Node.constant(1)
      else:
        Node.constant(0)
    of NodeAdd:
      let children = node.children
        .map(child => child.derive(varName))
        .filter(child => not child.isConst(0))
      
      if children.len == 0:
        Node.constant(0)
      elif children.len == 1:
        children[0]
      else:
        Node.new(NodeAdd, children)
    of NodeMul:
      if node.children.len == 0:
        Node.constant(0)
      elif node.children.len == 1:
        node.children[0].derive(varName)
      else:
        let
          a = Node.new(NodeMul, node.children[0..^2])
          b = node.children[^1]
        a.derive(varName) * b + b.derive(varName) * a
    of NodeNegate:
      -node.children[0].derive(varName)
    of NodeReciprocal:
      -Node.new(NodeReciprocal, (node.children[0] ^ Node.constant(2))) * node.children[0].derive(varName)
    of NodePow:
      # (f(x) ^ g(x))' = (e^(ln(f(x))*g(x))'
      # = e^(ln(f(x))*g(x)) * (ln(f(x)) * g'(x) + f'(x)/f(x) * g(x))
      # = (f(x) ^ g(x)) * (ln(f(x)) * g'(x) + f'(x)/f(x) * g(x))
      
      # Some examples to test if it works:
      #   1. (x ^ 2)' = x ^ 2 * (ln(x) * 0 + 2 / x) = x ^ 2 * 2/x = 2x
      #   2. (e ^ x)' = e ^ x * (ln(e) * 1 + 0 / e * x) = ln(e) * e ^ x = 1 * e^x = e ^ x
      
      let
        f = node.children[0]
        g = node.children[1]
      
      if g.isConst():
        g * f ^ (g - Node.constant(1))
      else:
        f ^ g * (ln(f) * g.derive(varName) + f.derive(varName) / f * g)
    of NodeMod:
      node.children[0].derive(varName)
    of NodeSin:
      let f = node.children[0]
      cos(f) * f.derive(varName)
    of NodeCos:
      let f = node.children[0]
      -sin(f) * f.derive(varName)
    of NodeFloor, NodeCeil:
      Node.constant(0)
    of NodeLn:
      let f = node.children[0]
      f.derive(varName) / f
    else:
      raise newException(ValueError, "Unable to derive " & $node.kind)

type
  ValueKind = enum
    ValueNumber, ValueFunction, ValueTuple
  
  Value*[T] = object
    case kind: ValueKind:
      of ValueNumber:
        number: T
      of ValueFunction:
        args: seq[string]
        body: Node
        closure: Table[string, Value[T]]
      of ValueTuple:
        fields: seq[Value[T]]

proc asNumber*[T](value: Value[T]): T =
  if value.kind != ValueNumber:
    raise newException(ValueError, "Value is not a number")
  result = value.number

proc initNumber*[T](_: typedesc[Value[T]], number: T): Value[T] =
  result = Value[T](kind: ValueNumber, number: number)

proc eval*[T](node: Node, vars: Table[string, Value[T]]): Value[T] =
  case node.kind:
    of NodeConst: Value[T].initNumber(T(node.value))
    of NodeVar:
      case node.name:
        of "pi": Value.initNumber(T(PI)) # TODO: Find a better system for constants
        of "e": Value.initNumber(T(E))
        else:
          if node.name notin vars:
            raise newException(ValueError, "Variable undefined")
          vars[node.name]
    of NaryNodes:
      let
        children = node.children.map(child => child.eval(vars).asNumber())
        res = case node.kind:
          of NodeAdd: sum(children)
          of NodeMul: prod(children)
          of NodeMax: max(children)
          of NodeMin: min(children)
          else:
            raise newException(ValueError, "Unreachable")
      Value.initNumber(res)
    of UnaryNodes:
      let
        value = node.children[0].eval(vars).asNumber()
        res = case node.kind:
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
      Value.initNumber(res)
    of BinaryNodes:
      let
        a = node.children[0].eval(vars).asNumber()
        b = node.children[1].eval(vars).asNumber()
      case node.kind:
        of NodePow: Value.initNumber(pow(a, b))
        of NodeMod: Value.initNumber(a mod b)
        else:
          raise newException(ValueError, "Unreachable")
    of NodeCall:
      let
        callee = node.children[0].eval(vars)
        args = node.children[1..^1].map(arg => arg.eval(vars))
      
      if callee.kind != ValueFunction:
        raise newException(ValueError, "Unable to call " & $callee.kind)
      
      var env = callee.closure
      for it, arg in args:
        env[callee.args[it]] = arg
      
      callee.body.eval(env)
    of NodeTuple:
      let fields = node.children.map(child => child.eval(vars))
      Value[T](kind: ValueTuple, fields: fields)
    of NodeLambda:
      Value[T](kind: ValueFunction,
        args: node.args,
        body: node.children[0],
        closure: vars
      )
    of NodeDerive:
      let function = node.children[0].eval(vars)
      
      if function.kind != ValueFunction:
        raise newException(ValueError, "Unable to derive " & $function.kind)
      
      let body = function.body.derive(function.args[node.argIndex])
      Value[T](kind: ValueFunction,
        args: function.args,
        body: body,
        closure: function.closure
      )

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
    of NodeCall:
      terms[0] & "(" & terms[1..^1].join(",") & ")"
    of NodeTuple:
      if terms.len == 1:
        "(" & terms[0] & ",)"
      else:
        "(" & terms.join(",") & ")"
    of NodeDerive:
      terms[0] & "'"
    else:
      FUNCTION_NAMES[node.kind] & "(" & terms.join(",") & ")"
  
  if LEVELS[node.kind] < level:
    result = "(" & result & ")"

proc `$`*(node: Node): string = node.stringify(0)

# Parser

proc parse*(source: string): Node =
  # Tokenization
  
  type
    TokenKind = enum
      TokenInt, TokenFractional, TokenName,
      TokenOp, TokenPrefixOp,
      TokenParOpen, TokenParClose,
      TokenBracketOpen, TokenBracketClose,
      TokenComma, TokenSemicolon, TokenColon,
      TokenSingleQuote
    
    Token = object
      kind: TokenKind
      value: string
  
  proc tokenize(source: string): seq[Token] =
    const
      OP_CHARS = {'+', '-', '*', '/', '^', '%', '<', '>', '='}
      WHITESPACE = {' ', '\n', '\t', '\r'}
      SINGLE_CHAR_TOKENS = {'(', ')', '[', ']', ',', ';', '\'', ':'}
    
    var it = 0
    
    proc readDigits(): string =
      while it < source.len and (source[it] in '0'..'9' or source[it] == '_'):
        result.add(source[it])
        it += 1
    
    template singleChar(tokenKind: TokenKind) =
      result.add(Token(kind: tokenKind))
      it += 1
    
    while it < source.len:
      case source[it]:
        of WHITESPACE:
          it += 1
        of '(': singleChar(TokenParOpen)
        of ')': singleChar(TokenParClose)
        of '[': singleChar(TokenBracketOpen)
        of ']': singleChar(TokenBracketClose)
        of ',': singleChar(TokenComma)
        of ';': singleChar(TokenSemicolon)
        of '\'': singleChar(TokenSingleQuote)
        of ':': singleChar(TokenColon)
        of OP_CHARS:
          var isPrefix = (it > 0 and source[it - 1] in WHITESPACE + {'(', ',', ';'} or it == 0)
          
          var op = ""
          while it < source.len and source[it] in OP_CHARS:
            op.add(source[it])
            it += 1
          
          isPrefix = isPrefix and it < source.len and source[it] notin WHITESPACE
          
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
  
  proc parseType(stream: var TokenStream): Type =
    if stream.take(TokenName):
      if stream.value == "Fn":
        result = Type(kind: TypeFunction)
  
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
      
      if result.isNil:
        result = Node.new(NodeTuple)
      elif stream.next(TokenComma):
        result = Node.new(NodeTuple, result)
        while stream.take(TokenComma):
          let item = stream.parse(0)
          if item.isNil:
            break
          result.children.add(item)
      
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
    
    while (result.typeHint.isKind(TypeFunction) and stream.next(TokenParOpen)) or
          stream.next(TokenSingleQuote) or
          stream.next(TokenColon):
      if stream.take(TokenSingleQuote):
        # Derive
        result = Node.derive(result)
      elif stream.take(TokenColon):
        # Type Annotation
        let typ = stream.parseType()
        if typ.isNil:
          return nil
        result.typeHint = typ
      else:
        # Call function
        let args = stream.parseArguments()
        if args.isNone:
          return nil
        result = Node.call(result, args.get())
    
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
            of "->": 1
            else: return nil
        
        if opLevel < level:
          stream.cur -= 1
          return
        
        if op == "->":
          # Lambda
          let
            args = case result.kind:
              of NodeVar: @[result.name]
              of NodeTuple: result.children.map(arg => arg.name)
              else: return nil
            body = stream.parse(opLevel)
          if body.isNil:
            return nil
          result = Node.lambda(args, body)
        else:
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
        valueA = a.eval(toTable({"x": Value.initNumber(x)})).number
        valueB = b(x)
      if abs(valueA - valueB) > eps:
        echo valueA, " ", valueB
        return false
    return true
  
  proc equals(a, b: Node,
              domain: HSlice[float, float] = -10.0..10.0,
              steps: int = 10,
              eps: float = 0.0001): bool =
    result = equals(a, x => b.eval(toTable({"x": Value.initNumber(x)})).number,
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
  assert equals(parse("sqrt(x)"), parse("x^(1/2)"))
  assert equals(parse("cbrt(x)"), parse("x^(1/3)"))
  assert equals(parse("cbrt(x^2)"), parse("x^(2/3)"))
  
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

  # Tests / Lambda
  
  assert equals(parse("(x -> x ^ 2)(x + 1)"), x => (x + 1) ^ 2)
  assert equals(parse("((x, y) -> x + y)(x, x^2)"), x => x + x ^ 2)
  assert equals(parse("(x -> y -> x + y)(x)(x^2)"), x => x + x ^ 2)
  assert equals(parse("(x -> y -> z -> x + y + z)(x)(x^2)(-2)"), x => x + x ^ 2 - 2)
  assert equals(parse("(x -> (y, z) -> x + y + z)(x)(x^2, -2)"), x => x + x ^ 2 - 2)
  assert equals(parse("(x -> f -> (f: Fn)(x))(x)(x -> x ^ 2)"), x => x ^ 2)

  # Tests / Derive
  
  # Tests / Derive / Polynomial
  assert equals(parse("(x -> x + 1)'(x)"), x => 1.0)
  assert equals(parse("(x -> x ^ 2)'(x)"), x => 2 * x)
  assert equals(parse("(x -> x ^ 3 - 2x)'(x)"), x => 3 * x^2 - 2)
  assert equals(parse("(x -> x * x * x - 2x^2 / x)'(x)"), x => 3 * x^2 - 2)
  
  # Tests / Derive / Exponential
  assert equals(parse("(x -> x ^ 10)'(x)"), x => 10 * x ^ 9)
  assert equals(parse("(x -> x ^ (-1))'(x)"), x => -1 / x ^ 2)
  assert equals(parse("(x -> e ^ x)'(x)"), x => exp(x))
  assert equals(parse("(x -> e ^ -x)'(x)"), x => -exp(-x))
  assert equals(parse("(x -> e ^ (x^2))'(x)"), x => exp(x ^ 2) * 2 * x, domain = -2.5..2.5)
  assert equals(parse("(x -> x ^ x)'(x)"), x => pow(x, x) * (ln(x) + 1), domain = 0.01..2.0)
  assert equals(parse("(x -> ln(3x))'(x)"), x => 1 / x)
  
  # Tests / Derive / Trigonometry
  assert equals(parse("(x -> sin(x)/cos(x))'(x)"), x => 1 / cos(x) ^ 2)
  assert equals(parse("(x -> sin(x ^ 2))'(x)"), x => cos(x ^ 2) * 2 * x)
  assert equals(parse("(x -> cos(x ^ 2))'(x)"), x => -sin(x ^ 2) * 2 * x)
