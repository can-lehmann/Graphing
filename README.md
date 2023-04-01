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
- Sums and Products: E.g. `sum(0, 10, n -> (-1)^n * (x^(2n)) / (prod(1, 2n, i -> i)))`
- Lambda expressions: E.g. `(x -> x ^ 2)(x - 1)`
- Compute exact derivatives: E.g. `(x -> x ^ 3 - 2x)'(x)`

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

