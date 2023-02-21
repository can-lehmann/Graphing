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

import std/[tables, sets, sequtils, sugar, math, strformat, strutils, random, options]
import owlkettle, owlkettle/[adw, cairo, dataentries]
import geometrymath

# Utilities

proc peek[T](hashSet: HashSet[T]): T =
  for item in hashSet:
    return item

proc isInf(x: float): bool =
  result = x == Inf or x == NegInf

# Utilities/Viewport

type Viewport = ref object
  center: Vec2
  height: float
  size: Vec2
  region: Box2

proc map(view: Viewport, pos: Vec2): Vec2 =
  let
    aspect = view.size.x / view.size.y
    size = Vec2(x: view.height * aspect, y: view.height)
  result = (pos - view.center) / size * view.size
  result.y *= -1
  result += view.size / 2

proc mapReverse(view: Viewport, pos: Vec2): Vec2 =
  let
    aspect = view.size.x / view.size.y
    size = Vec2(x: view.height * aspect, y: view.height)
  result = pos - view.size / 2
  result.y *= -1
  result = result * size / view.size + view.center

proc update(view: var Viewport, size: tuple[width, height: int]) =
  view.size = Vec2(x: size.width.float, y: size.height.float)
  view.region = Box2(
    min: view.mapReverse(Vec2(y: view.size.y)),
    max: view.mapReverse(Vec2(x: view.size.x))
  )

# Utilities/Colors

type Color = tuple[r, g, b, a: float]

proc rgb(_: typedesc[Color], r, g, b: float): Color =
  result = (r, g, b, 1.0)

proc rgb(_: typedesc[Color], hex: int): Color =
  let
    r = ((hex shr 16) and 0xff) / 255
    g = ((hex shr 8) and 0xff) / 255
    b = (hex and 0xff) / 255
  result = (r, g, b, 1.0)

# Utilities/Cairo

proc moveTo(ctx: CairoContext, pos: Vec2) = ctx.moveTo(pos.x, pos.y)
proc lineTo(ctx: CairoContext, pos: Vec2) = ctx.lineTo(pos.x, pos.y)

proc rectangle(ctx: CairoContext, box: Box2) =
  ctx.rectangle(box.min.x, box.min.y, box.size.x, box.size.y)

# Utilities/Vec2Entry

viewable Vec2Entry:
  value: Vec2
  
  proc changed(value: Vec2)

method view(entry: Vec2EntryState): Widget =
  result = gui:
    Box:
      orient = OrientX
      style = {BoxLinked}
      
      NumberEntry:
        value = entry.value.x
        xAlign = 1.0
        maxWidth = 4
        
        proc changed(value: float) =
          entry.value.x = value
          if not entry.changed.isNil:
            entry.changed.callback(entry.value)
      
      NumberEntry:
        value = entry.value.y
        xAlign = 1.0
        maxWidth = 4
        
        proc changed(value: float) =
          entry.value.y = value
          if not entry.changed.isNil:
            entry.changed.callback(entry.value)

# Config

const
  APP_NAME = "Graphing"
  
  BACKGROUND_COLOR = Color.rgb(0xffffff)
  GRID_COLOR = Color.rgb(0xdeddda)
  AXIS_COLOR = Color.rgb(0x000000)
  
  GRID_WIDTH = 2.0
  AXIS_WIDTH = 2.0
  TICK_SIZE = 3.0
  TICK_DIST = 70.0
  LABEL_SIZE = 12.0
  GRAPH_LINE_WIDTH = 3.0
  
  ZOOM_SPEED = 1.5
  SMOOTH_ZOOM_SPEED = 1.01
  
  COLORS = [
    Color.rgb(0x1c71d8), # Blue
    Color.rgb(0x2ec27e), # Green
    Color.rgb(0xe66100), # Orange
    Color.rgb(0xe01b24), # Red
  ]

# Node

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
  
  Node = ref object
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

proc eval[T](node: Node, vars: Table[string, T]): T =
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

proc `$`(node: Node): string = node.stringify(0)

proc new(_: typedesc[Node], kind: NodeKind, children: varargs[Node]): Node =
  result = Node(kind: kind, children: @children)

proc constant(_: typedesc[Node], value: int): Node =
  result = Node(kind: NodeConst, value: value)

proc `-`(a: Node): Node = Node.new(NodeNegate, a)

proc `+`(a, b: Node): Node = Node.new(NodeAdd, a, b)
proc `-`(a, b: Node): Node = Node.new(NodeAdd, a, -b)
proc `*`(a, b: Node): Node = Node.new(NodeMul, a, b)
proc `/`(a, b: Node): Node = Node.new(NodeMul, a, Node.new(NodeReciprocal, b))
proc `^`(a, b: Node): Node = Node.new(NodePow, a, b)
proc `mod`(a, b: Node): Node = Node.new(NodeMod, a, b)

proc x(_: typedesc[Node]): Node = Node(kind: NodeVar, name: "x")

# Node / Parser

proc parse(source: string): Node =
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

# Graphs

type Graph = ref object of RootObj
  name: string

method draw(graph: Graph, view: Viewport, ctx: CairoContext) {.base.} = discard
method view(graph: Graph): Widget {.base.} = discard

type FunctionGraph = ref object of Graph
  text: string
  tree: Node
  error: bool
  
  color: Color
  lineWidth: float

proc new(_: typedesc[FunctionGraph],
         name: string,
         text: string = "",
         color: Color = COLORS[0],
         lineWidth: float = GRAPH_LINE_WIDTH): FunctionGraph =
  result = FunctionGraph(
    name: name,
    text: text,
    color: color,
    lineWidth: lineWidth
  )
  if text.len > 0:
    result.tree = text.parse()

method title(graph: FunctionGraph): string {.base.} =
  result = graph.name & "(x)"

method drawPath(graph: FunctionGraph, view: Viewport, ctx: CairoContext) {.base.} =
  const STEP_SIZE = 5.0
  
  var screenX = view.map(Vec2()).x mod STEP_SIZE
  if screenX > 0:
    screenX -= STEP_SIZE
    
  var isStart = true
  while screenX < view.size.x + STEP_SIZE:
    let
      x = view.mapReverse(Vec2(x: screenX)).x
      y = graph.tree.eval(toTable({"x": x}))
    
    if isNaN(y) or isInf(y):
      isStart = true
      screenX += STEP_SIZE
      continue
    
    let pos = view.map(Vec2(x: x, y: y))
    if isStart:
      ctx.moveTo(pos)
      isStart = false
    else:
      ctx.lineTo(pos)
    
    screenX += STEP_SIZE

method draw(graph: FunctionGraph, view: Viewport, ctx: CairoContext) =
  if graph.tree.isNil:
    return
  
  try:
    graph.drawPath(view, ctx)
    graph.error = false
  except CatchableError as err:
    echo err.msg
    graph.error = true
  
  ctx.source = graph.color
  ctx.lineWidth = graph.lineWidth
  ctx.stroke()

method view(graph: FunctionGraph): Widget =
  result = gui:
    EntryRow:
      title = graph.title()
      text = graph.text
      
      if graph.tree.isNil or graph.error:
        style = {EntryError}
      else:
        style = {}
      
      proc changed(text: string) =
        graph.text = text
        graph.tree = parse(text)
      
      MenuButton {.addSuffix.}:
        icon = "view-more-symbolic"
        style = {ButtonFlat}
        
        Popover:
          sizeRequest = (250, -1)
          
          Box:
            orient = OrientY
            margin = 6
            spacing = 6
            
            PreferencesGroup:
              title = "General"
              
              ActionRow:
                title = "Name"
                
                Entry {.addSuffix.}:
                  text = graph.name
                  maxWidth = 6
                  proc changed(text: string) =
                    graph.name = text
            
            PreferencesGroup:
              title = "Display"
              
              ActionRow:
                title = "Line Width"
                
                NumberEntry {.addSuffix.}:
                  value = graph.lineWidth
                  maxWidth = 6
                  xAlign = 1
                  
                  proc changed(lineWidth: float) =
                    graph.lineWidth = lineWidth
              
              ActionRow:
                title = "Color"
                subtitle = "of the line"
                
                ColorButton {.addSuffix.}:
                  color = graph.color
                  useAlpha = true
                  proc changed(color: Color) =
                    graph.color = color

type PolarGraph = ref object of FunctionGraph

proc new(_: typedesc[PolarGraph],
         name: string,
         text: string = "",
         color: Color = COLORS[0],
         lineWidth: float = GRAPH_LINE_WIDTH): PolarGraph =
  result = PolarGraph(
    name: name,
    text: text,
    color: color,
    lineWidth: lineWidth
  )
  if text.len > 0:
    result.tree = text.parse()

method title(graph: PolarGraph): string =
  result = graph.name & "(phi)"

method drawPath(graph: PolarGraph, view: Viewport, ctx: CairoContext) =
  const STEPS = 128
  
  var isStart = true
  for it in 0..STEPS:
    let
      phi = 2.0 * PI * (it / STEPS)
      r = graph.tree.eval(toTable({"phi": phi}))
    
    if isNaN(r) or isInf(r):
      isStart = true
      continue
    
    let pos = view.map(Vec2(x: cos(phi), y: sin(phi)) * r)
    if isStart:
      ctx.moveTo(pos)
      isStart = false
    else:
      ctx.lineTo(pos)

# GraphView

# GraphView / Grid

type Grid = ref object
  shown: bool
  
  backgroundColor: Color
  gridColor: Color
  axisColor: Color

proc new(_: typedesc[Grid]): Grid =
  result = Grid(
    shown: true,
    backgroundColor: BACKGROUND_COLOR,
    gridColor: GRID_COLOR,
    axisColor: AXIS_COLOR
  )

proc guessGridSize(view: Viewport): tuple[precision: int, size: Vec2] =
  let
    tickCount = floor(view.size / TICK_DIST)
    optimalSize = view.region.size / tickCount
    precision = floor(log10(optimalSize.x))
    magnitude = pow(10.0, precision)
  
  result.precision = max(-int(precision), 0)
  
  var minDelta = Inf
  for factor in [1, 2, 5]:
    let
      size = magnitude * float(factor)
      delta = abs(size - optimalSize.x)
    if delta < minDelta:
      result.size = Vec2(x: size, y: size)
      minDelta = delta

proc formatLabel(value: float, precision: int): string =
  result.formatValue(value, "." & $max(1, precision) & "f")

proc draw(grid: Grid, view: Viewport, ctx: CairoContext) =
  ctx.rectangle(Box2(max: view.size))
  ctx.source = grid.backgroundColor
  ctx.fill()
  
  if grid.shown:
    let
      (precision, size) = guessGridSize(view)
      min = floor(view.region.min / size).toIndex2()
      max = ceil(view.region.max / size).toIndex2()
    
    block backgroundGrid:
      for x in min.x..max.x:
        let pos = view.map(Vec2(x: float(x) * size.x))
        ctx.moveTo(pos.dup(y = 0))
        ctx.lineTo(pos.dup(y = view.size.y))
      
      for y in min.y..max.y:
        let pos = view.map(Vec2(y: float(y) * size.y))
        ctx.moveTo(pos.dup(x = 0))
        ctx.lineTo(pos.dup(x = view.size.x))
      
      ctx.lineWidth = GRID_WIDTH
      ctx.source = grid.gridColor
      ctx.stroke()
    
    block axis:
      let origin = view.map(Vec2())
      
      ctx.moveTo(origin.dup(x = 0))
      ctx.lineTo(origin.dup(x = view.size.x))
      
      ctx.moveTo(origin.dup(y = 0))
      ctx.lineTo(origin.dup(y = view.size.y))
      
      ctx.lineWidth = AXIS_WIDTH
      ctx.source = grid.axisColor
      ctx.stroke()
    
    block ticks:
      for x in min.x..max.x:
        let pos = view.map(Vec2(x: float(x) * size.x))
        ctx.moveTo(pos + Vec2(y: -TICK_SIZE))
        ctx.lineTo(pos + Vec2(y: TICK_SIZE))
      
      for y in min.y..max.y:
        let pos = view.map(Vec2(y: float(y) * size.y))
        ctx.moveTo(pos + Vec2(x: -TICK_SIZE))
        ctx.lineTo(pos + Vec2(x: TICK_SIZE))
      
      ctx.lineWidth = AXIS_WIDTH
      ctx.source = grid.axisColor
      ctx.stroke()
    
    block labels:
      ctx.fontSize = LABEL_SIZE
      
      for x in min.x..max.x:
        if x == 0:
          continue
        let
          pos = view.map(Vec2(x: float(x) * size.x))
          label = formatLabel(float(x) * size.x, precision)
          width = ctx.textExtents(label).width.float
        ctx.moveTo(pos + Vec2(x: -width / 2, y: TICK_SIZE + LABEL_SIZE))
        ctx.text(label)
      
      for y in min.y..max.y:
        if y == 0:
          continue
        let
          pos = view.map(Vec2(y: float(y) * size.y))
          label = formatLabel(float(y) * size.y, precision)
          height = ctx.textExtents(label).height.float
        ctx.moveTo(pos + Vec2(x: TICK_SIZE * 2, y: height / 2))
        ctx.text(label)
      
      ctx.source = grid.axisColor
      ctx.fill()

# GraphView / Mouse

type Mouse = object
  pos: Vec2
  buttons: array[3, bool]

# GraphView / GraphView

viewable GraphView:
  graphs: seq[Graph]
  grid: Grid = Grid.new()
  mouse: Mouse
  viewport: Viewport = Viewport(height: 10.0)

method view(graphView: GraphViewState): Widget =
  result = gui:
    DrawingArea:
      proc draw(ctx: CairoContext, size: tuple[width, height: int]): bool =
        graphView.viewport.update(size)
        let view = graphView.viewport
        
        graphView.grid.draw(view, ctx)
        
        for graph in graphView.graphs:
          graph.draw(view, ctx)
      
      proc mousePressed(event: ButtonEvent): bool =
        if event.button in 0..<graphView.mouse.buttons.len:
          graphView.mouse.buttons[event.button] = true
      
      proc mouseReleased(event: ButtonEvent): bool =
        if event.button in 0..<graphView.mouse.buttons.len:
          graphView.mouse.buttons[event.button] = false
      
      proc mouseMoved(event: MotionEvent): bool =
        let pos = Vec2(x: event.x, y: event.y)
        if graphView.mouse.buttons[0]:
          let
            view = graphView.viewport
            delta = view.mapReverse(pos) - view.mapReverse(graphView.mouse.pos)
          graphView.viewport.center -= delta
        graphView.mouse.pos = pos
      
      proc scroll(event: ScrollEvent): bool =
        case event.direction:
          of ScrollUp: graphView.viewport.height *= ZOOM_SPEED
          of ScrollDown: graphView.viewport.height /= ZOOM_SPEED
          of ScrollSmooth:
            graphView.viewport.height *= pow(SMOOTH_ZOOM_SPEED, event.dy)
          else: discard

# AppMenu

viewable AppMenu:
  discard

method view(menu: AppMenuState): Widget =
  result = gui:
    MenuButton:
      icon = "open-menu"
      style = {ButtonFlat}
      
      PopoverMenu:
        Box:
          orient = OrientY
          
          ModelButton:
            text = "New"
          
          ModelButton:
            text = "Open"
          
          ModelButton:
            text = "Save"
          
          Separator()
          
          ModelButton:
            text = "About " & APP_NAME

# ViewMenu

viewable ViewMenu:
  grid: Grid
  viewport: Viewport

method view(menu: ViewMenuState): Widget =
  result = gui:
    MenuButton:
      icon = "view-grid"
      style = {ButtonFlat}
      
      Popover:
        sizeRequest = (300, -1)
        
        Box:
          orient = OrientY
          margin = 6
          spacing = 6
          
          PreferencesGroup:
            title = "Viewport"
            
            ActionRow:
              title = "Center"
              
              Vec2Entry {.addSuffix.}:
                value = menu.viewport.center
                proc changed(value: Vec2) =
                  menu.viewport.center = value
            
            ActionRow:
              title = "Height"
              
              NumberEntry {.addSuffix.}:
                value = menu.viewport.height
                xAlign = 1.0
                maxWidth = 6
                
                proc changed(value: float) =
                  menu.viewport.height = value

# Main Application

viewable App:
  graphs: seq[Graph] = @[
    Graph FunctionGraph.new("f", "x ^ 2")
  ]
  
  grid: Grid = Grid.new()
  viewport: Viewport = Viewport(height: 10.0)


proc findFreeName(graphs: seq[Graph]): string =
  var names = toHashSet(["f", "g", "h"])
  for graph in graphs:
    names.excl(graph.name)
  
  if names.len > 0:
    result = names.peek()
  else:
    # Append an index to f (like f1, f2, ...)
    var maxIndex = 0
    for graph in graphs:
      if graph.name.len > 1 and
         graph.name[0] == 'f' and
         graph.name[1..^1].allIt(it in '0'..'9'):
        let index = graph.name[1..^1].parseInt()
        if index > maxIndex:
          maxIndex = index
    
    result = "f" & $(maxIndex + 1)

method view(app: AppState): Widget =
  result = gui:
    WindowSurface:
      defaultSize = (1200, 700)
    
      Box:
        orient = OrientX
        
        Box {.expand: false.}:
          orient = OrientY
          sizeRequest = (330, -1)
          
          HeaderBar {.expand: false.}:
            showTitleButtons = false
            
            SplitButton {.addLeft.}:
              icon = "list-add"
              style = {ButtonFlat}
              
              PopoverMenu:
                Box:
                  orient = OrientY
                  
                  ModelButton:
                    text = "Polar Graph"
                    proc clicked() =
                      let name = app.graphs.findFreeName()
                      app.graphs.add(PolarGraph.new(name, color=sample(COLORS)))
              
              proc clicked() =
                let name = app.graphs.findFreeName()
                app.graphs.add(FunctionGraph.new(name, color=sample(COLORS)))
          
          ScrolledWindow:
            PreferencesGroup:
              margin = 12
              
              for graph in app.graphs:
                insert(graph.view())
        
        Separator() {.expand: false.}
        
        Box:
          orient = OrientY
          
          HeaderBar {.expand: false.}:
            WindowTitle {.addTitle.}:
              title = APP_NAME
              subtitle = $app.graphs.len & " graphs"
            
            AppMenu() {.addRight.}
            ViewMenu {.addRight.}:
              grid = app.grid
              viewport = app.viewport
            
            Button {.addRight.}:
              icon = "zoom-in-symbolic"
              style = {ButtonFlat}
              
              proc clicked() =
                app.viewport.height /= ZOOM_SPEED
            
            Button {.addRight.}:
              icon = "zoom-out-symbolic"
              style = {ButtonFlat}
              
              proc clicked() =
                app.viewport.height *= ZOOM_SPEED
          
          Box:
            orient = OrientY
            
            GraphView:
              graphs = app.graphs
              grid = app.grid
              viewport = app.viewport

adw.brew(gui(App()))
