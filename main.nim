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

import std/[tables, sets, sequtils, sugar, strformat, strutils, random, math, os]
import owlkettle, owlkettle/[adw, cairo, dataentries]
import geometrymath
import algebra

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

proc clone(viewport: Viewport): Viewport =
  Viewport(
    center: viewport.center,
    height: viewport.height,
    size: viewport.size,
    region: viewport.region
  )

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

proc map(view: Viewport, box: Box2): Box2 =
  result = Box2(
    min: view.map(box.min),
    max: view.map(box.max)
  )

proc updateRegion(view: Viewport) =
  view.region = Box2(
    min: view.mapReverse(Vec2(y: view.size.y)),
    max: view.mapReverse(Vec2(x: view.size.x))
  )

proc update(view: Viewport, size: tuple[width, height: int]) =
  view.size = Vec2(x: size.width.float, y: size.height.float)
  view.updateRegion()

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

proc circle(ctx: CairoContext, pos: Vec2, radius: float64) =
  ctx.circle(pos.x, pos.y, radius)

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
  TRACE_POINT_RADIUS = 5.0
  
  ZOOM_SPEED = 1.5
  SMOOTH_ZOOM_SPEED = 1.01
  
  COLORS = [
    Color.rgb(0x1c71d8), # Blue
    Color.rgb(0x2ec27e), # Green
    Color.rgb(0xe66100), # Orange
    Color.rgb(0xe01b24), # Red
  ]

# Graphs

type Graph = ref object of RootObj
  name: string

method draw(graph: Graph, view: Viewport, ctx: CairoContext) {.base.} = discard
method view(graph: Graph): Widget {.base.} = discard

# Trace

type Trace = object
  valid: bool
  pos: Vec2
  color: Color

method trace(graph: Graph, pos: Vec2): Trace {.base.} = discard

proc init(_: typedesc[Trace], pos: Vec2, color: Color): Trace =
  if isNaN(pos.x) or isInf(pos.x) or
     isNaN(pos.y) or isInf(pos.y):
    result = Trace(valid: false)
  else:
    result = Trace(
      valid: true,
      pos: pos,
      color: color
    )

proc draw(trace: Trace, view: Viewport, ctx: CairoContext) =
  if not trace.valid:
    return
  
  let pos = view.map(trace.pos)
  ctx.moveTo(pos)
  ctx.circle(pos,TRACE_POINT_RADIUS)
  ctx.source = trace.color
  ctx.fill()


# Graphs / Function Graph

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
      y = graph.tree.eval(toTable({"x": Value.initNumber(x)})).asNumber()
    
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

method trace(graph: FunctionGraph, pos: Vec2): Trace =
  if graph.tree.isNil:
    return Trace(valid: false)
  
  try:
    let y = graph.tree.eval(toTable({"x": Value.initNumber(pos.x)})).asNumber()
    result = Trace.init(Vec2(x: pos.x, y: y), graph.color)
  except CatchableError as err:
    result = Trace(valid: false)

# Graphs / Polar Graph

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
      r = graph.tree.eval(toTable({"phi": Value.initNumber(phi)})).asNumber()
    
    if isNaN(r) or isInf(r):
      isStart = true
      continue
    
    let pos = view.map(Vec2(x: cos(phi), y: sin(phi)) * r)
    if isStart:
      ctx.moveTo(pos)
      isStart = false
    else:
      ctx.lineTo(pos)

method trace(graph: PolarGraph, pos: Vec2): Trace =
  if graph.tree.isNil:
    return Trace(valid: false)
  
  try:
    var phi = arctan2(pos.y, pos.x)
    if phi < 0.0:
      phi += 2 * PI
    let r = graph.tree.eval(toTable({"phi": Value.initNumber(phi)})).asNumber()
    result = Trace.init(Vec2(x: cos(phi), y: sin(phi)) * r, graph.color)
  except CatchableError as err:
    result = Trace(valid: false)

# Graphs / Implicit Graph

type ImplicitGraph = ref object of FunctionGraph

proc new(_: typedesc[ImplicitGraph],
         name: string,
         text: string = "",
         color: Color = COLORS[0],
         lineWidth: float = GRAPH_LINE_WIDTH): ImplicitGraph =
  result = ImplicitGraph(
    name: name,
    text: text,
    color: color,
    lineWidth: lineWidth
  )
  if text.len > 0:
    result.tree = text.parse()

method title(graph: ImplicitGraph): string =
  result = graph.name & "(x, y) = 0"

method draw(graph: ImplicitGraph, view: Viewport, ctx: CairoContext) =
  if graph.tree.isNil:
    return
  
  const
    MAX_DEPTH = 5
    DIVS = 2
  
  proc draw(region: Box2, depth: int) =
    if depth <= 0:
      ctx.rectangle(view.map(region))
    else:
      for y in 0..<DIVS:
        for x in 0..<DIVS:
          let
            size = region.size / DIVS.float64
            pos = region.min + size * Index2(x: x, y: y).toVec2()
            subregion = Box2(min: pos, max: pos + size)
          
          let inter = graph.tree.eval({
            "x": Value.initNumber(subregion.xInter()),
            "y": Value.initNumber(subregion.yInter())
          }.toTable()).asNumber()
          
          if 0 in inter:
            draw(subregion, depth - 1)
  
  try:
    let
      smallestRect = view.region.size / float64(DIVS ^ MAX_DEPTH)
      region = Box2(
        min: floor(view.region.min / smallestRect) * smallestRect,
        max: ceil(view.region.max / smallestRect) * smallestRect
      )
    draw(region, MAX_DEPTH)
    ctx.source = graph.color
    ctx.fill()
    graph.error = false
  except ValueError:
    graph.error = true

method trace(graph: ImplicitGraph, pos: Vec2): Trace =
  discard

# GraphView

# GraphView / Grid

type Grid = ref object
  showGrid: bool
  showAxes: bool
  
  backgroundColor: Color
  gridColor: Color
  axisColor: Color

proc new(_: typedesc[Grid]): Grid =
  result = Grid(
    showGrid: true,
    showAxes: true,
    backgroundColor: BACKGROUND_COLOR,
    gridColor: GRID_COLOR,
    axisColor: AXIS_COLOR
  )

proc guessGridSize(view: Viewport): tuple[precision: int, size: Vec2] =
  const EPS = 0.000000001
  
  let
    tickCount = floor(view.size / TICK_DIST)
    optimalSize = view.region.size / tickCount
  if tickCount.x < 1 or optimalSize.x < EPS:
    return (0, Vec2(x: 1, y: 1))
  
  let
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
  
  let
    (precision, size) = guessGridSize(view)
    min = floor(view.region.min / size).toIndex2()
    max = ceil(view.region.max / size).toIndex2()
  
  if grid.showGrid:
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
  
  if grid.showAxes:
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
  tracing: bool

method view(graphView: GraphViewState): Widget =
  result = gui:
    DrawingArea:
      proc draw(ctx: CairoContext, size: tuple[width, height: int]): bool =
        graphView.viewport.update(size)
        let view = graphView.viewport
        
        graphView.grid.draw(view, ctx)
        
        for graph in graphView.graphs:
          graph.draw(view, ctx)
        
        if graphView.tracing:
          for graph in graphView.graphs:
            graph.trace(view.mapReverse(graphView.mouse.pos)).draw(view, ctx)
      
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


# Project

type Project = ref object
  graphs: seq[Graph]
  path: string

proc add(project: Project, graph: Graph) =
  project.graphs.add(graph)

proc findFreeName(project: Project): string =
  var names = toHashSet(["f", "g", "h"])
  for graph in project.graphs:
    names.excl(graph.name)
  
  if names.len > 0:
    result = names.peek()
  else:
    # Append an index to f (like f1, f2, ...)
    var maxIndex = 0
    for graph in project.graphs:
      if graph.name.len > 1 and
         graph.name[0] == 'f' and
         graph.name[1..^1].allIt(it in '0'..'9'):
        let index = graph.name[1..^1].parseInt()
        if index > maxIndex:
          maxIndex = index
    
    result = "f" & $(maxIndex + 1)

# Viewport Preferences

viewable ViewportPreferences:
  viewport: Viewport

method view(preferences: ViewportPreferencesState): Widget =
  let viewport = preferences.viewport
  result = gui:
    PreferencesGroup:
      title = "Viewport"
      
      Button {.addSuffix.}:
        icon = "zoom-fit-best-symbolic"
        style = {ButtonFlat}
        
        proc clicked() =
          viewport.center = Vec2()
          viewport.height = 10.0
      
      ActionRow:
        title = "Center"
        
        Vec2Entry {.addSuffix.}:
          value = viewport.center
          proc changed(value: Vec2) =
            viewport.center = value
      
      ActionRow:
        title = "Height"
        
        NumberEntry {.addSuffix.}:
          value = viewport.height
          xAlign = 1.0
          maxWidth = 6
          
          proc changed(value: float) =
            viewport.height = value

# Grid Preferences

viewable GridPreferences:
  grid: Grid

method view(preferences: GridPreferencesState): Widget =
  let grid = preferences.grid
  result = gui:
    PreferencesGroup:
      title = "Grid"
      
      ActionRow:
        title = "Background"
        
        ColorButton {.addSuffix.}:
          color = grid.backgroundColor
          proc changed(color: Color) =
            grid.backgroundColor = color
      
      ActionRow:
        title = "Show Grid"
        
        Switch {.addSuffix.}:
          state = grid.showGrid
          proc changed(state: bool) =
            grid.showGrid = state
      
      ActionRow:
        title = "Grid Color"
        
        ColorButton {.addSuffix.}:
          color = grid.gridColor
          proc changed(color: Color) =
            grid.gridColor = color
      
      ActionRow:
        title = "Show Axes"
        
        Switch {.addSuffix.}:
          state = grid.showAxes
          proc changed(state: bool) =
            grid.showAxes = state
      
      ActionRow:
        title = "Axis Color"
        
        ColorButton {.addSuffix.}:
          color = grid.axisColor
          proc changed(color: Color) =
            grid.axisColor = color


# Export Dialog

viewable ExportDialog:
  project: Project
  viewport: Viewport
  grid: Grid = Grid.new()

proc renderPixbuf(dialog: ExportDialogState): Pixbuf =
  let view = dialog.viewport
  if view.size.x <= 0 or view.size.y <= 0:
    return nil
  
  let
    surface = newImageSurface(FormatRGB24,
      int(dialog.viewport.size.x),
      int(dialog.viewport.size.y)
    )
    ctx = newCairoContext(surface)
  
  view.updateRegion()
  dialog.grid.draw(view, ctx)
  
  for graph in dialog.project.graphs:
    graph.draw(view, ctx)
  
  let
    pixelCount = surface.width * surface.height
    imageData = cast[ptr UncheckedArray[uint32]](surface.data)
  
  var data = newSeq[uint8](3 * pixelCount)
  for it in 0..<pixelCount:
    data[3 * it] = uint8((imageData[it] shr 16) and 0xff) # Red
    data[3 * it + 1] = uint8((imageData[it] shr 8) and 0xff) # Green
    data[3 * it + 2] = uint8(imageData[it] and 0xff) # Blue
  result = newPixbuf(surface.width, surface.height, data)
  
  defer:
    ctx.destroy()
    surface.destroy()

method view(dialog: ExportDialogState): Widget =
  result = gui:
    Dialog:
      title = "Export"
      
      DialogButton {.addButton.}:
        text = "Cancel"
        res = DialogCancel
      
      DialogButton {.addButton.}:
        text = "Export"
        res = DialogAccept
        style = {ButtonSuggested}
      
      Box:
        orient = OrientX
        
        ScrolledWindow {.expand: false.}:
          sizeRequest = (270, -1)
          Box:
            orient = OrientY
            margin = 12
            spacing = 6
            
            PreferencesGroup {.expand: false.}:
              title = "Image"
              
              ActionRow:
                title = "Width"
                
                NumberEntry {.addSuffix.}:
                  value = dialog.viewport.size.x
                  maxWidth = 6
                  xAlign = 1.0
                  proc changed(value: float64) =
                    dialog.viewport.size.x = value
              
              ActionRow:
                title = "Height"
                
                NumberEntry {.addSuffix.}:
                  value = dialog.viewport.size.y
                  maxWidth = 6
                  xAlign = 1.0
                  proc changed(value: float64) =
                    dialog.viewport.size.y = value
            
            ViewportPreferences {.expand: false.}:
              viewport = dialog.viewport
            
            GridPreferences {.expand: false.}:
              grid = dialog.grid
        
        Separator() {.expand: false.}
        
        let pixbuf = dialog.renderPixbuf()
        if pixbuf.isNil:
          Label(text = "Unable to render")
        else:
          Picture:
            pixbuf = pixbuf

# AppMenu

viewable AppMenu:
  project: Project
  viewport: Viewport

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
            text = "Export"
            
            proc clicked() =
              # Show export dialog
              let (res, state) = menu.app.open:
                gui:
                  ExportDialog:
                    project = menu.project
                    viewport = menu.viewport.clone()
              
              if res.kind != DialogAccept:
                return
              
              let exportDialog = ExportDialogState(state)
              
              # Ask where to save the image
              let (fileRes, fileState) = menu.app.open:
                gui:
                  FileChooserDialog:
                    action = FileChooserSave
                    
                    DialogButton {.addButton.}:
                      text = "Export"
                      res = DialogAccept
                      style = {ButtonSuggested}
                    
                    DialogButton {.addButton.}:
                      text = "Cancel"
                      res = DialogCancel
              
              if fileRes.kind != DialogAccept:
                return
              
              # Save image
              let
                path = FileChooserDialogState(fileState).filename
                pixbuf = exportDialog.renderPixbuf()
                (dir, name, ext) = path.splitFile()
                fileType = case ext.toLowerAscii():
                  of ".png": "png"
                  of ".jpg", ".jpeg": "jpeg"
                  else:
                    raise newException(ValueError, "Unsupported file type: \"" & ext & "\"")
              
              pixbuf.save(path, fileType)
          
          Separator()
          
          ModelButton:
            text = "About " & APP_NAME

# Display Options

type DisplayOptions = ref object
  tracing: bool

# ViewMenu

viewable ViewMenu:
  grid: Grid
  viewport: Viewport
  options: DisplayOptions

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
            title = "Display"
            
            ActionRow:
              title = "Grid"
              
              Switch {.addSuffix.}:
                state = menu.grid.showGrid
                proc changed(state: bool) =
                  menu.grid.showGrid = state
            
            ActionRow:
              title = "Axes"
              
              Switch {.addSuffix.}:
                state = menu.grid.showAxes
                proc changed(state: bool) =
                  menu.grid.showAxes = state
            
            ActionRow:
              title = "Tracing"
              
              Switch {.addSuffix.}:
                state = menu.options.tracing
                proc changed(state: bool) =
                  menu.options.tracing = state
          
          ViewportPreferences(viewport = menu.viewport)

# Main Application

viewable App:
  project: Project = Project(graphs: @[
    Graph FunctionGraph.new("f", "x ^ 2"),
    #Graph ImplicitGraph.new("g", "(x + y) ^ 2 + y ^ 2 - 1")
  ])
  
  grid: Grid = Grid.new()
  viewport: Viewport = Viewport(height: 10.0)
  displayOptions: DisplayOptions = DisplayOptions()

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
                      let name = app.project.findFreeName()
                      app.project.add(PolarGraph.new(name, color=sample(COLORS)))
                  
                  ModelButton:
                    text = "Implicit Graph"
                    proc clicked() =
                      let name = app.project.findFreeName()
                      app.project.add(ImplicitGraph.new(name, color=sample(COLORS)))
              
              proc clicked() =
                let name = app.project.findFreeName()
                app.project.add(FunctionGraph.new(name, color=sample(COLORS)))
          
          ScrolledWindow:
            PreferencesGroup:
              margin = 12
              
              for graph in app.project.graphs:
                insert(graph.view())
        
        Separator() {.expand: false.}
        
        Box:
          orient = OrientY
          
          HeaderBar {.expand: false.}:
            WindowTitle {.addTitle.}:
              title = APP_NAME
              
              if app.project.path.len == 0:
                subtitle = $app.project.graphs.len & " graphs"
              else:
                subtitle = $app.project.path
            
            AppMenu {.addRight.}:
              project = app.project
              viewport = app.viewport
            
            ViewMenu {.addRight.}:
              grid = app.grid
              viewport = app.viewport
              options = app.displayOptions
            
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
              graphs = app.project.graphs
              grid = app.grid
              viewport = app.viewport
              tracing = app.displayOptions.tracing

adw.brew(gui(App()))
