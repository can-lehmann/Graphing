# Graphing

A simple graphing application built with owlkettle.

![Screenshot](assets/screenshot.png)

## Features

- Basic graphing
- Interactive viewport
- Polar Plots
- Tracing
- Supported Functions: `sin`, `cos`, `tan`, `floor`, `ceil`, `abs`, `max`, `min`, `sqrt`, `cbrt`, `ln`
- Operators: `+`, `-`, `*`, `/`, `^` (exponentiation), `%` (modulo)
- Constants: `pi`, `e`

## Installation

```bash
$ git clone https://github.com/can-lehmann/Graphing.git
$ cd Graphing
$ nimble install owlkettle@#head
$ nimble install geometrymath
$ nim compile -r -d:adwaita12 main
```

## License

Graphing is licensed under the MIT license.
See `LICENSE.txt` for more information.

