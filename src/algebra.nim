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
import geometrymath

# Intervals

{.push inline.}
proc contains*(inter: Inter, value: float64): bool =
  inter.min <= value and inter.max >= value

proc `+`*(a, b: Inter): Inter =
  Inter(min: a.min + b.min, max: a.max + b.max)

proc `-`*(a, b: Inter): Inter =
  Inter(min: a.min - b.max, max: a.max - b.min)

proc `-`*(a: Inter): Inter =
  Inter(min: -a.max, max: -a.min)

proc `*`*(a, b: Inter): Inter =
  let vals = [
    a.min * b.min,
    a.max * b.min,
    a.min * b.max,
    a.max * b.max
  ]
  
  Inter(
    min: min(vals),
    max: max(vals)
  )

proc reciprocal*(inter: Inter): Inter =
  if 0.0 in inter:
    Inter(min: -Inf, max: Inf)
  else:
    Inter(
      min: 1.0 / inter.max,
      max: 1.0 / inter.min
    )

proc min*(a, b: Inter): Inter =
  Inter(min: min(a.min, b.min), max: min(a.max, b.max))

proc max*(a, b: Inter): Inter =
  Inter(min: max(a.min, b.min), max: max(a.max, b.max))

proc sin*(x: Inter): Inter = Inter(min: -1.0, max: 1.0) # TODO
proc cos*(x: Inter): Inter = Inter(min: -1.0, max: 1.0) # TODO
proc tan*(x: Inter): Inter = Inter(min: -Inf, max: Inf) # TODO

proc arcsin*(x: Inter): Inter =
  Inter(
    min: arcsin(clamp(x.min, -1, 1)),
    max: arcsin(clamp(x.max, -1, 1))
  )

proc arccos*(x: Inter): Inter =
  Inter(
    min: arccos(clamp(x.max, -1, 1)),
    max: arccos(clamp(x.min, -1, 1))
  )

proc arctan*(x: Inter): Inter = Inter(min: arctan(x.min), max: arctan(x.max))

proc floor*(a: Inter): Inter =
  Inter(min: floor(a.min), max: floor(a.max))

proc ceil*(a: Inter): Inter =
  Inter(min: ceil(a.min), max: ceil(a.max))

proc abs*(a: Inter): Inter =
  Inter(min: max(0.0, max(a.min, -a.max)), max: max(-a.min, a.max))

proc ln*(a: Inter): Inter =
  Inter(
    min: if a.min <= 0.0: -Inf else: ln(a.min),
    max: if a.max <= 0.0: -Inf else: ln(a.max)
  )

proc exp*(a: Inter): Inter =
  Inter(min: exp(a.min), max: exp(a.max))

proc pow*(a, b: Inter): Inter =
  let vals = [
    pow(a.min, b.min),
    pow(a.max, b.min),
    pow(a.min, b.max),
    pow(a.max, b.max)
  ]
  result = Inter(min: min(vals), max: max(vals))
  if 0.0 in a:
    result.min = min(result.min, 0.0)
    result.max = max(result.max, 0.0)

proc `mod`*(a, b: Inter): Inter =
  Inter(min: -b.max, max: b.max) # TODO
{.pop.}

proc prod*(inters: openArray[Inter]): Inter =
  result = Inter(min: 1.0, max: 1.0)
  for inter in inters:
    result = result * inter

proc min*(inters: openArray[Inter]): Inter =
  result = Inter(min: Inf, max: Inf)
  for inter in inters:
    result = min(result, inter)

proc max*(inters: openArray[Inter]): Inter =
  result = Inter(min: -Inf, max: -Inf)
  for inter in inters:
    result = max(result, inter)

# float64

{.push inline.}

proc reciprocal*(x: float64): float64 =
  1.0 / x

{.pop.}

# Types

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

# Node

type
  NodeKind = enum
    NodeConst, NodeVar
    NodeAdd, NodeMul,
    NodeNegate, NodeReciprocal,
    NodePow, NodeMod,
    NodeSin, NodeCos, NodeTan,
    NodeArcSin, NodeArcCos, NodeArcTan,
    NodeFloor, NodeCeil, NodeAbs,
    NodeMax, NodeMin,
    NodeLn,
    NodeSum, NodeProd,
    NodeCall
    NodeLambda,
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
    NodeArcSin, NodeArcCos, NodeArcTan,
    NodeFloor, NodeCeil, NodeAbs,
    NodeLn
  }
  BinaryNodes = {
    NodePow, NodeMod
  }

# Node / Constructors

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

# Node / Utils

proc findVariables(node: Node): HashSet[string] =
  case node.kind:
    of NodeVar: result = toHashSet([node.name])
    else:
      for child in node.children:
        result = result.union(child.findVariables())

# Node / Derive

proc `$`*(node: Node): string

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
    of NodeSum:
      var lambda = node.children[2]
      if lambda.kind != NodeLambda:
        raise newException(ValueError, "Unable to derive " & $lambda.kind & " in sum")
      if lambda.args[0] == varName:
        Node.constant(0)
      else:
        lambda = Node.lambda(lambda.args, lambda.children[0].derive(varName))
        Node.new(NodeSum, [node.children[0], node.children[1], lambda])
    else:
      raise newException(ValueError, "Unable to derive " & $node.kind)

# Node / Evaluate

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

proc asInt*(value: Value[float64]): int =
  if value.kind != ValueNumber:
    raise newException(ValueError, "Value is not a number")
  result = int(value.number)

proc asInt*(value: Value[Inter]): int =
  if value.kind != ValueNumber:
    raise newException(ValueError, "Value is not a number")
  if value.number.min != value.number.max:
    raise newException(ValueError, "Value is not a single integer")
  result = int(value.number.min)


proc call*[T](callee: Value[T], args: openArray[Value[T]]): Value[T] =
  if callee.kind != ValueFunction:
    raise newException(ValueError, "Unable to call " & $callee.kind)
  
  var env = callee.closure
  for it, arg in args:
    env[callee.args[it]] = arg
  
  result = callee.body.eval(env)

proc initNumber*[T](_: typedesc[Value[T]], value: T): Value[T] =
  result = Value[T](kind: ValueNumber, number: value)

proc initNumber*(_: typedesc[Value[Inter]], value: float64): Value[Inter] =
  result = Value[Inter].initNumber(Inter(
    min: value,
    max: value
  ))

proc initNumber*(_: typedesc[Value[Inter]], value: int): Value[Inter] =
  result = Value[Inter].initNumber(float64(value))

proc initNumber*[T](_: typedesc[Value[T]], value: int): Value[T] =
  result = Value[T].initNumber(T(value))

proc sum*[T](min, max, lambda: Value[T]): Value[T] =
  result = Value[T].initNumber(0)
  for it in min.asInt()..max.asInt():
    result.number = result.number + lambda.call([Value[T].initNumber(it)]).asNumber()

proc prod*[T](min, max, lambda: Value[T]): Value[T] =
  result = Value[T].initNumber(1)
  for it in min.asInt()..max.asInt():
    result.number = result.number * lambda.call([Value[T].initNumber(it)]).asNumber()


proc eval*[T](node: Node, vars: Table[string, Value[T]]): Value[T] =
  case node.kind:
    of NodeConst: Value[T].initNumber(node.value)
    of NodeVar:
      case node.name:
        of "pi": Value[T].initNumber(PI) # TODO: Find a better system for constants
        of "e": Value[T].initNumber(E)
        else:
          if node.name notin vars:
            raise newException(ValueError, "Variable \"" & node.name & "\" undefined")
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
      Value[T].initNumber(res)
    of UnaryNodes:
      if node.children.len != 1:
        raise newException(ValueError, $node.kind & " expects one argument but got " & $node.children.len)
      let
        value = node.children[0].eval(vars).asNumber()
        res = case node.kind:
          of NodeNegate: -value
          of NodeReciprocal: reciprocal(value)
          of NodeSin: sin(value)
          of NodeCos: cos(value)
          of NodeTan: tan(value)
          of NodeArcSin: arcsin(value)
          of NodeArcCos: arccos(value)
          of NodeArcTan: arctan(value)
          of NodeFloor: floor(value)
          of NodeCeil: ceil(value)
          of NodeAbs: abs(value)
          of NodeLn: ln(value)
          else:
            raise newException(ValueError, "Unreachable")
      Value[T].initNumber(res)
    of BinaryNodes:
      if node.children.len != 2:
        raise newException(ValueError, $node.kind & " expects two arguments but got " & $node.children.len)
      let
        a = node.children[0].eval(vars).asNumber()
        b = node.children[1].eval(vars).asNumber()
      case node.kind:
        of NodePow: Value[T].initNumber(pow(a, b))
        of NodeMod: Value[T].initNumber(a mod b)
        else:
          raise newException(ValueError, "Unreachable")
    of NodeCall:
      let
        callee = node.children[0].eval(vars)
        args = node.children[1..^1].map(arg => arg.eval(vars))
      callee.call(args)
    of NodeLambda:
      Value[T](kind: ValueFunction,
        args: node.args,
        body: node.children[0],
        closure: vars
      )
    of NodeSum, NodeProd:
      if node.children.len != 3:
        raise newException(ValueError, $node.kind & " expects three arguments but got " & $node.children.len)
      let
        min = node.children[0].eval(vars)
        max = node.children[1].eval(vars)
        lambda = node.children[2].eval(vars)
      
      case node.kind:
        of NodeSum: sum(min, max, lambda)
        of NodeProd: prod(min, max, lambda)
        else:
          raise newException(ValueError, "Unreachable")
    of NodeTuple:
      let fields = node.children.map(child => child.eval(vars))
      Value[T](kind: ValueTuple, fields: fields)
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

# Node / Print

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
    NodeArcSin: "arcsin",
    NodeArcCos: "arccos",
    NodeArcTan: "arctan",
    NodeFloor: "floor",
    NodeCeil: "ceil",
    NodeAbs: "abs",
    NodeMax: "max",
    NodeMin: "min",
    NodeLn: "ln",
    NodeSum: "sum",
    NodeProd: "prod"
  ]
  
  let
    level = if ord(node.kind) in ord(low(LEVELS))..ord(high(LEVELS)): LEVELS[node.kind] + 1 else: 0
    terms = node.children.map(child => child.stringify(level))
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
      terms[0] & "(" & terms[1..^1].join(", ") & ")"
    of NodeLambda:
      var args = node.args.join(", ")
      if node.args.len != 1:
        args = "(" & args & ")"
      args & " -> " & terms[0]
    of NodeTuple:
      if terms.len == 1:
        "(" & terms[0] & ",)"
      else:
        "(" & terms.join(", ") & ")"
    of NodeDerive:
      terms[0] & "'"
    else:
      FUNCTION_NAMES[node.kind] & "(" & terms.join(", ") & ")"
  
  if level < level:
    result = "(" & result & ")"

proc `$`*(node: Node): string = node.stringify(0)

# LaTeX

proc flatten(node: Node, kind: NodeKind): seq[Node] =
  if node.kind == kind:
    for child in node.children:
      result.add(child.flatten(kind))
  else:
    result = @[node]

proc toLaTeX(node: Node, level: int): string =
  const
    TOP_LEVEL = 0
    ADD_LEVEL = 4
    MUL_LEVEL = 5
    POW_LEVEL = 6
    CONST_LEVEL = 10
  
  var maxLevel = CONST_LEVEL
  case node.kind:
    of NodeConst:
      if node.value < 0:
        maxLevel = ADD_LEVEL
      else:
        maxLevel = CONST_LEVEL
      result = $node.value
    of NodeVar:
      maxLevel = CONST_LEVEL
      result = node.name
    of NodeAdd:
      case node.children.len:
        of 0:
          maxLevel = CONST_LEVEL
          result = "0"
        of 1:
          maxLevel = CONST_LEVEL
          result = node.children[0].toLaTeX(level)
        else:
          maxLevel = ADD_LEVEL
          for it, child in node.flatten(NodeAdd):
            let (isNeg, term) = 
              case child.kind:
                of NodeConst:
                  if child.value < 0:
                    (true, Node.constant(-child.value))
                  else:
                    (false, child)
                of NodeNegate: (true, child.children[0])
                else: (false, child)
            
            if it != 0:
              if isNeg:
                result.add(" - ")
              else:
                result.add(" + ")
            else:
              if isNeg:
                result.add("-")
                maxLevel = TOP_LEVEL
            
            result.add(term.toLaTeX(if isNeg: POW_LEVEL else: ADD_LEVEL))
    of NodeMul:
      var
        num: seq[Node] = @[]
        den: seq[Node] = @[]
      for child in node.flatten(NodeMul):
        if child.kind == NodeReciprocal:
          den.add(child.children[0])
        else:
          num.add(child)
      
      if den.len > 0:
        let
          top = Node.new(NodeMul, num).toLaTeX(TOP_LEVEL)
          bottom = Node.new(NodeMul, den).toLaTeX(TOP_LEVEL)
        
        maxLevel = CONST_LEVEL
        result = "\\frac{" & top & "}{" & bottom & "}"
      else:
        case num.len:
          of 0:
            maxLevel = CONST_LEVEL
            result = "1"
          of 1: 
            maxLevel = CONST_LEVEL
            result = num[0].toLaTeX(level)
          else:
            maxLevel = MUL_LEVEL
            result = num
              .map(child => child.toLaTeX(MUL_LEVEL))
              .join(" \\cdot ")
    of NodeNegate:
      maxLevel = 0
      result = "-" & node.children[0].toLaTeX(CONST_LEVEL)
    of NodeReciprocal:
      maxLevel = 10
      result = "\\frac{1}{" & node.children[0].toLaTeX(TOP_LEVEL) & "}"
    of NodePow:
      let
        base = node.children[0].toLaTeX(CONST_LEVEL)
        exp = node.children[1].toLaTeX(TOP_LEVEL)
      maxLevel = POW_LEVEL
      result = "{" & base & "} ^ {" & exp & "}"
    of NodeMod:
      maxLevel = MUL_LEVEL
      result = node.children[0].toLaTeX(MUL_LEVEL) &
               " \\mathrm{mod} " &
               node.children[0].toLaTeX(CONST_LEVEL)
    of NodeSin, NodeCos, NodeTan, 
       NodeArcSin, NodeArcCos, NodeArcTan, 
       NodeMin, NodeMax, NodeLn:
      let
        name = case node.kind:
          of NodeSin: "\\sin"
          of NodeCos: "\\cos"
          of NodeTan: "\\tan"
          of NodeArcSin: "\\arcsin"
          of NodeArcCos: "\\arccos"
          of NodeArcTan: "\\arctan"
          of NodeMin: "\\min"
          of NodeMax: "\\max"
          of NodeLn: "\\ln"
          else: raise newException(ValueError, "Unreachable")
        args = node.children
          .map(child => child.toLaTeX(TOP_LEVEL))
          .join(", ")
      
      maxLevel = CONST_LEVEL
      result = name & "(" & args & ")"
    of NodeFloor, NodeCeil, NodeAbs:
      if node.children.len != 1:
        raise newException(ValueError, $node.kind & " expects one argument but got " & $node.children.len)
      
      let (left, right) = case node.kind:
        of NodeFloor: ("\\lfloor ", " \\rfloor")
        of NodeCeil: ("\\lceil ", " \\rceil")
        of NodeAbs: ("|", "|")
        else: raise newException(ValueError, "Unreachable")
      
      maxLevel = CONST_LEVEL
      result = left & node.children[0].toLaTeX(TOP_LEVEL) & right
    of NodeSum, NodeProd:
      if node.children.len != 3:
        raise newException(ValueError, $node.kind & " expects three arguments but got " & $node.children.len)
      
      let symbol = case node.kind:
        of NodeSum: "\\sum"
        of NodeProd: "\\prod"
        else: raise newException(ValueError, "Unreachable")
      
      if node.children[2].kind == NodeLambda:
        let
          iter = node.children[2].args[0]
          init = iter & " = " & node.children[0].toLaTeX(TOP_LEVEL)
          stop = node.children[1].toLaTeX(TOP_LEVEL)
          body = node.children[2].children[0].toLaTeX(POW_LEVEL)
        
        maxLevel = CONST_LEVEL
        result = symbol & "_{" & init & "}^{" & stop & "} " & body
      else:
        raise newException(ValueError, "Unable to generate LaTeX")
    of NodeCall:
      let
        callee = node.children[0].toLaTeX(CONST_LEVEL)
        args = node.children[1..^1]
          .map(child => child.toLaTeX(TOP_LEVEL))
          .join(", ")
      
      result = callee & "(" & args & ")"
    of NodeLambda:
      var args = node.args.join(", ")
      if node.args.len != 1:
        args = "(" & args & ")"
      
      let body = node.children[0].toLaTeX(TOP_LEVEL)
      
      maxLevel = TOP_LEVEL
      result = args & " \\rightarrow " & body
    of NodeTuple:
      let items = node.children
        .map(child => child.toLaTeX(TOP_LEVEL))
        .join(", ")
      
      maxLevel = CONST_LEVEL
      result = "(" & items & ")"
    of NodeDerive:
      maxLevel = CONST_LEVEL
      result = node.children[0].toLaTeX(CONST_LEVEL) & "'"
  
  if level > maxLevel:
    result = "(" & result & ")"

proc toLaTeX*(node: Node): string =
  result = node.toLaTeX(0)

# Parser

proc parse*(source: string): Node {.raises: [ValueError].} =
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
  
  proc parse(stream: var TokenStream, level: int, allowPrefix: bool = true): Node {.raises: [ValueError].}
  
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
        of "asin", "arcsin": result = Node(kind: NodeArcSin)
        of "acos", "arccos": result = Node(kind: NodeArcCos)
        of "atan", "arctan": result = Node(kind: NodeArcTan)
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
        of "sum": result = Node(kind: NodeSum)
        of "prod": result = Node(kind: NodeProd)
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
  
  assert equals(parse("arcsin(x)"), arcsin, domain = -1.0..1.0)
  assert equals(parse("asin(x)"), arcsin, domain = -1.0..1.0)
  assert equals(parse("arcsin(0)"), 0)
  assert equals(parse("arcsin(1)"), PI / 2)
  assert equals(parse("arcsin(-1)"), -PI / 2)
  
  # Tests / Cos
  
  assert equals(parse("cos(x)"), cos)
  assert equals(parse("cos(0)"), 1)
  assert equals(parse("cos(pi / 2)"), 0)
  assert equals(parse("cos(pi)"), -1)
  assert equals(parse("cos(3/2 pi)"), 0)
  assert equals(parse("cos(2pi)"), 1)
  assert equals(parse("cos(2pi + x)"), parse("cos(x)"))
  
  assert equals(parse("arccos(x)"), arccos, domain = -1.0..1.0)
  assert equals(parse("acos(x)"), arccos, domain = -1.0..1.0)
  assert equals(parse("arccos(1)"), 0)
  assert equals(parse("arccos(0)"), PI / 2)
  assert equals(parse("arccos(-1)"), PI)
  
  # Tests / Tan
  
  assert equals(parse("tan(x)"), tan)
  
  assert equals(parse("arctan(x)"), arctan)
  assert equals(parse("atan(x)"), arctan)
  assert equals(parse("tan(arctan(x))"), (x: float64) => x)
  
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
  
  # Tests / Sum
  
  assert equals(parse("sum(0, 10, x -> x)"), 55)
  assert equals(parse("sum(1, 3, x -> x ^ 3)"), 1 + 8 + 27)
  assert equals(parse("sum(10, 10, x -> x)"), 10)
  assert equals(parse("sum(10, 9, x -> x)"), 0)
  assert equals(parse("sum(0, 3, i -> 1)"), 4)
  assert equals(parse("sum(0, 10, n -> (-1)^n * (x^(2n)) / (prod(1, 2n, i -> i)))"), x => cos(x), -5.0..5.0)
  
  # Tests / Prod
  
  assert equals(parse("prod(0, 10, x -> x)"), 0)
  assert equals(parse("prod(1, 4, x -> x)"), 24)
  assert equals(parse("prod(1, 3, x -> x ^ 3)"), 1 * 8 * 27)
  assert equals(parse("prod(10, 10, x -> x)"), 10)
  assert equals(parse("prod(10, 9, x -> x)"), 1)

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
  
  # Tests / Derive / Sum
  assert equals(parse("(x -> sum(0, 3, i -> 1))'(x)"), x => 0.0)
  assert equals(parse("(x -> sum(0, 3, i -> x))'(x)"), x => 4.0)
  assert equals(parse("(x -> sum(0, 3, i -> x ^ i))'(x)"), x => 3 * x ^ 2 + 2 * x + 1)
  
  # Tests / LaTeX
  
  # Tests / LaTeX / Base
  assert parse("a + b * c").toLaTeX() == "a + b \\cdot c"
  assert parse("(a + b) * c").toLaTeX() == "(a + b) \\cdot c"
  
  # Tests / LaTeX / Add
  assert parse("a + b + c").toLaTeX() == "a + b + c"
  assert parse("a - b - c").toLaTeX() == "a - b - c"
  assert parse("-a - b - c").toLaTeX() == "-a - b - c"
  assert parse("a + (-b) + (-c) + d").toLaTeX() == "a - b - c + d"
  assert parse("a - (b + c) - d").toLaTeX() == "a - (b + c) - d"
  assert parse("-(b + c) - d").toLaTeX() == "-(b + c) - d"
  assert parse("(b + c) - d").toLaTeX() == "b + c - d"
  
  # Tests / LaTeX / Mul
  assert parse("(a + b) * c / d / e").toLaTeX() == "\\frac{(a + b) \\cdot c}{d \\cdot e}"
  assert parse("(a + b) * c / (d * e) / f").toLaTeX() == "\\frac{(a + b) \\cdot c}{d \\cdot e \\cdot f}"
  assert parse("a / (b / c)").toLaTeX() == "\\frac{a}{\\frac{b}{c}}"
  
  # Tests / LaTeX / Pow
  assert parse("x ^ 2").toLaTeX() == "{x} ^ {2}"
  assert parse("(3 * x) ^ (2 + x)").toLaTeX() == "{(3 \\cdot x)} ^ {2 + x}"
  
  # Tests / LaTeX / Sum
  assert parse("sum(0, 3, n -> x^n)").toLaTeX() == "\\sum_{n = 0}^{3} {x} ^ {n}"
  assert parse("sum(0, 10, n -> 1 / 2^n)").toLaTeX() == "\\sum_{n = 0}^{10} \\frac{1}{{2} ^ {n}}"
  
  # Tests / LaTeX / Prod
  assert parse("prod(1, 4, x -> x)").toLaTeX() == "\\prod_{x = 1}^{4} x"
  
  # Tests / LaTeX / Lambda
  assert parse("(x -> x ^ 2)'(x)").toLaTeX() == "(x \\rightarrow {x} ^ {2})'(x)"
