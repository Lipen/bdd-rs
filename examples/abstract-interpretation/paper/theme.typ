// Theme and styling for the research paper
// Modern, clean design with emphasis on readability

#import "@preview/numbly:0.1.0"
#import "@preview/cetz:0.4.2"

// Counters for numbered environments
#let theorem-counter = counter("theorem")
#let definition-counter = counter("definition")
#let property-counter = counter("property")

// Mathematical symbols - define custom symbols for lattice operations
#let ljoin = $union.sq$      // ⊔ - join (least upper bound)
#let lmeet = $inter.sq$      // ⊓ - meet (greatest lower bound)
#let widen = $nabla$         // ∇ - widening
#let lle = $subset.eq.sq$    // ⊑ - less-than-or-equal (partial order)
#let implies = $arrow.r.double$  // ⇒ - implication

// Color palette - Modern academic blue-gray theme
#let colors = (
  primary: rgb("#2563eb"), // Vibrant blue
  secondary: rgb("#64748b"), // Slate gray
  accent: rgb("#0891b2"), // Cyan
  text: rgb("#0f172a"), // Almost black
  text-light: rgb("#475569"), // Light gray for captions
  code-bg: rgb("#f1f5f9"), // Light blue-gray background
  warning: rgb("#f59e0b"), // Amber
  success: rgb("#10b981"), // Emerald
  error: rgb("#ef4444"), // Red
  background: rgb("#ffffff"), // White
  line: rgb("#e2e8f0"), // Light border
)

// Typography settings
#let fonts = (
  body: "Libertinus Serif",
  sans: "Noto Sans",
  mono: "JetBrains Mono",
  math: "New Computer Modern Math",
)

// Spacing and layout
#let spacing = (
  tiny: 0.25em,
  small: 0.5em,
  medium: 1em,
  large: 1.5em,
  xlarge: 2em,
)

// Colored True/False
#let True = text(colors.success)[`true`]
#let False = text(colors.error)[`false`]

// Colored checkmark/crossmark
#let YES = text(colors.success)[#sym.checkmark]
#let NO = text(colors.error)[#sym.crossmark]

// Aliases
#let rel(x) = math.class("relation", x)
#let nrel(x) = rel(math.cancel(x))

// Document styling function
#let apply-theme(
  doc,
  running-head: none,
) = {
  set text(
    font: fonts.body,
    size: 11pt,
    fill: colors.text,
    lang: "en",
    hyphenate: true,
  )

  set page(
    paper: "a4",
    margin: (
      top: 2.5cm,
      bottom: 2.5cm,
      left: 2.5cm,
      right: 2.5cm,
    ),
    numbering: "1",
    number-align: center,
    header: context {
      if running-head != none {
        if counter(page).get().first() > 1 {
          set text(size: 0.82em, fill: colors.text-light)
          line(length: 100%, stroke: 0.5pt + colors.line)
          v(-0.5em)
          [#running-head]
        }
      }
    },
  )

  set par(
    justify: true,
    leading: 0.65em,
    spacing: 1.2em,
  )

  // Headings
  set heading(numbering: "1.")

  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    set text(
      font: fonts.sans,
      size: 1.64em,
      weight: "bold",
      fill: colors.primary,
    )
    block(
      above: spacing.xlarge,
      below: spacing.large,
      it,
    )
  }

  show heading.where(level: 2): it => {
    set text(
      font: fonts.sans,
      size: 1.27em,
      weight: "semibold",
      fill: colors.primary,
    )
    block(
      above: spacing.large,
      below: spacing.medium,
      it,
    )
  }

  show heading.where(level: 3): it => {
    set text(
      font: fonts.sans,
      size: 1.09em,
      weight: "semibold",
      fill: colors.secondary,
    )
    block(
      above: spacing.medium,
      below: spacing.small,
      it,
    )
  }

  // Code blocks
  show raw.where(block: true): it => {
    set text(
      font: fonts.mono,
      size: 0.86em,
    )
    block(
      fill: colors.code-bg,
      inset: spacing.medium,
      radius: 4pt,
      width: 100%,
      it,
    )
  }

  show raw.where(block: false): it => {
    box(
      fill: colors.code-bg,
      outset: (x: 3pt, y: 2pt),
      radius: 2pt,
      text(
        font: fonts.mono,
        size: 0.9em,
        fill: colors.primary,
        it,
      ),
    )
  }

  // Links
  show link: it => {
    set text(fill: colors.accent)
    underline(it)
  }

  // Lists
  set list(
    marker: ([•], [◦], [‣]),
    indent: 1em,
  )

  set enum(
    numbering: "1.a.i.",
    indent: 1em,
  )

  // Figures
  show figure: it => {
    set align(center)
    block(
      above: spacing.large,
      below: spacing.large,
      it,
    )
  }

  show figure.caption: it => {
    set text(
      size: 0.86em,
      fill: colors.text-light,
      style: "italic",
    )
    block(
      above: spacing.small,
      it,
    )
  }

  // Tables
  set table(
    stroke: (x, y) => if y == 0 {
      (bottom: 1.5pt + colors.primary)
    } else {
      (bottom: 0.5pt + colors.line)
    },
    fill: (x, y) => if y == 0 {
      colors.code-bg
    },
  )

  // Equations
  set math.equation(
    numbering: "(1)",
  )

  show math.equation.where(block: true): it => {
    block(
      above: spacing.medium,
      below: spacing.medium,
      it,
    )
  }

  // Fix emptyset symbol
  show sym.emptyset: set text(font: "Libertinus Sans")

  // Emphasis
  show emph: set text(fill: colors.accent)

  // Show i.e. in italic:
  show "i.e.": set text(style: "italic")
  // Show e.g. in italic:
  show "e.g.": set text(style: "italic")
  // Shot etc. in italic:
  show "etc.": set text(style: "italic")

  // Bibliography
  set bibliography(
    title: "References",
    style: "ieee",
  )

  doc
}

// Custom boxes for highlights
#let info-box(title: none, body) = {
  block(
    fill: colors.code-bg,
    stroke: (left: 3pt + colors.primary),
    inset: spacing.medium,
    radius: 4pt,
    width: 100%,
    {
      if title != none {
        text(
          font: fonts.sans,
          weight: "semibold",
          fill: colors.primary,
          size: 0.91em,
          title,
        )
        v(spacing.small)
      }
      body
    },
  )
}

#let example-box(title: "Example", body) = {
  block(
    fill: rgb("#f0fdf4"),
    stroke: (left: 3pt + colors.success),
    inset: spacing.medium,
    radius: 4pt,
    width: 100%,
    {
      text(
        font: fonts.sans,
        weight: "semibold",
        fill: colors.success,
        size: 0.91em,
        title,
      )
      v(spacing.small)
      body
    },
  )
}

#let warning-box(title: "Note", body) = {
  block(
    fill: rgb("#fffbeb"),
    stroke: (left: 3pt + colors.warning),
    inset: spacing.medium,
    radius: 4pt,
    width: 100%,
    {
      text(
        font: fonts.sans,
        weight: "semibold",
        fill: colors.warning,
        size: 0.91em,
        title,
      )
      v(spacing.small)
      body
    },
  )
}

// Theorem-like environments with auto-numbering
#let theorem(title: none, body) = {
  theorem-counter.step()
  let number = context theorem-counter.display()
  let display-title = if title != none {
    [Theorem #number (#title)]
  } else {
    [Theorem #number]
  }

  block(
    fill: rgb("#eff6ff"),
    stroke: (left: 3pt + colors.primary),
    inset: spacing.medium,
    radius: 4pt,
    width: 100%,
    {
      text(
        font: fonts.sans,
        weight: "bold",
        fill: colors.primary,
        size: 0.91em,
        display-title,
      )
      h(spacing.small)
      body
    },
  )
}

// Definition box with auto-numbering
#let definition(title: none, body) = {
  definition-counter.step()
  let number = context definition-counter.display()
  let display-title = if title != none {
    [Definition #number (#title)]
  } else {
    [Definition #number]
  }

  block(
    fill: rgb("#eff6ff"),
    stroke: (left: 3pt + colors.primary),
    inset: spacing.medium,
    radius: 4pt,
    width: 100%,
    {
      text(
        font: fonts.sans,
        weight: "bold",
        fill: colors.primary,
        size: 0.91em,
        display-title,
      )
      h(spacing.small)
      body
    },
  )
}

// Property box with auto-numbering
#let property(title: none, body) = {
  property-counter.step()
  let number = context property-counter.display()
  let display-title = if title != none {
    [Property #number (#title)]
  } else {
    [Property #number]
  }

  block(
    fill: rgb("#faf5ff"),
    stroke: (left: 3pt + rgb("#9333ea")),
    inset: spacing.medium,
    radius: 4pt,
    width: 100%,
    {
      text(
        font: fonts.sans,
        weight: "bold",
        fill: rgb("#9333ea"),
        size: 0.91em,
        display-title,
      )
      h(spacing.small)
      body
    },
  )
}

// Proof environment with left border and QED symbol
#let proof(body) = {
  block(
    stroke: (left: 2pt + colors.secondary),
    inset: (left: spacing.large, right: spacing.medium, top: spacing.small, bottom: spacing.small),
    width: 100%,
    {
      text(
        font: fonts.sans,
        weight: "semibold",
        style: "italic",
        fill: colors.secondary,
        size: 0.91em,
        [Proof.],
      )
      h(spacing.small)
      body
      h(1fr)
      box(
        baseline: 0.2em,
        square(
          size: 0.7em,
          fill: black,
        ),
      )
    },
  )
}

// Helper functions for paper structure
#let paper-title(content) = {
  align(center)[
    #block(
      above: 2em,
      below: 1em,
      text(
        size: 2em,
        weight: "bold",
        fill: colors.primary,
        font: fonts.sans,
        content,
      ),
    )
  ]
}

#let paper-authors(authors) = {
  align(center)[
    #text(
      size: 1.09em,
      font: fonts.sans,
      authors,
    )
  ]
}

#let paper-abstract(content) = {
  block(
    fill: colors.code-bg,
    inset: 1.8em,
    radius: 6pt,
    width: 100%,
  )[
    #text(
      font: fonts.sans,
      weight: "bold",
      size: 1.09em,
      fill: colors.primary,
      [Abstract],
    )
    #v(0.7em)

    #set par(justify: true, leading: 0.7em)
    #content
  ]
}

#let paper-keywords(..keywords) = {
  let ks = keywords.pos().map(box).join(" · ")

  align(center)[
    #text(
      size: 0.91em,
      fill: colors.text-light,
      style: "italic",
      font: fonts.sans,
      [*Keywords:* #ks],
    )
  ]
}

// ============================================================================
// Visualization Functions using CeTZ
// ============================================================================

/// Draw a BDD node
/// - id: Node identifier
/// - var: Variable name (e.g., "a", "x₁")
/// - pos: Position (x, y) tuple
/// - terminal: If true, draw as terminal node (0 or 1)
#let bdd-node(id, var, pos, terminal: false) = {
  import cetz: draw

  if terminal {
    // Terminal nodes: square boxes
    draw.rect(
      (pos.at(0) - 0.3, pos.at(1) - 0.25),
      (pos.at(0) + 0.3, pos.at(1) + 0.25),
      fill: if var == "1" { colors.success.lighten(60%) } else { colors.line },
      stroke: 1pt + if var == "1" { colors.success } else { colors.secondary },
      radius: 3pt,
      name: id,
    )
  } else {
    // Decision nodes: circles
    draw.circle(
      pos,
      radius: 0.35,
      fill: colors.primary.lighten(80%),
      stroke: 1.5pt + colors.primary,
      name: id,
    )
  }

  draw.content(
    pos,
    text(
      size: 0.9em,
      weight: if terminal { "bold" } else { "regular" },
      fill: if terminal and var == "1" { colors.success } else { colors.text },
      var,
    ),
  )
}

/// Draw a BDD edge
/// - from: Source node id
/// - to: Target node id
/// - low: If true, draw dashed (low/false edge), otherwise solid (high/true edge)
/// - label: Optional edge label
#let bdd-edge(from, to, low: false, label: none) = {
  import cetz: draw

  draw.line(
    (name: from, anchor: -90deg),
    (name: to, anchor: 90deg),
    stroke: if low {
      (paint: colors.secondary, thickness: 1pt, dash: "dashed")
    } else {
      (paint: colors.primary, thickness: 1.5pt)
    },
    mark: (end: ">", fill: if low { colors.secondary } else { colors.primary }),
  )

  if label != none {
    draw.content(
      ((name: from), 50%, (name: to)),
      anchor: "west",
      text(size: 0.75em, fill: colors.text-light, label),
    )
  }
}

/// Complete BDD diagram helper
/// Example usage:
/// #bdd-diagram(
///   nodes: (
///     (id: "a", var: "a", pos: (0, 0)),
///     (id: "b1", var: "b", pos: (-1, -1.5)),
///     (id: "c1", var: "c", pos: (-1.5, -3)),
///     (id: "1", var: "1", pos: (0, -4.5), terminal: true),
///     (id: "0", var: "0", pos: (-2.5, -4.5), terminal: true),
///   ),
///   edges: (
///     (from: "a", to: "b1", low: true),
///     (from: "a", to: "c1", low: false),
///     // ... more edges
///   ),
/// )
#let bdd-diagram(nodes: (), edges: (), caption: none, width: 100%, height: auto) = {
  figure(
    caption: caption,
    cetz.canvas({
      import cetz: draw

      // Draw all nodes
      for node in nodes {
        bdd-node(
          node.id,
          node.var,
          node.pos,
          terminal: node.at("terminal", default: false),
        )
      }

      // Draw all edges
      for edge in edges {
        bdd-edge(
          edge.from,
          edge.to,
          low: edge.at("low", default: false),
          label: edge.at("label", default: none),
        )
      }

      // Add legend
      draw.content(
        (-3.5, 1.2),
        anchor: "west",
        box(
          inset: 0.5em,
          radius: 3pt,
          stroke: colors.line,
          fill: white,
        )[
          #text(size: 0.75em)[
            #box(width: 1em, line(length: 1em, stroke: 1.5pt + colors.primary)) High (1) \
            #box(width: 1em, line(length: 1em, stroke: (dash: "dashed", paint: colors.secondary))) Low (0)
          ]
        ],
      )
    }),
  )
}

/// State machine diagram
/// Example:
/// #state-machine(
///   states: (
///     (id: "init", label: "INIT", pos: (0, 0)),
///     (id: "ready", label: "READY", pos: (2, 0)),
///   ),
///   transitions: (
///     (from: "init", to: "ready", label: "start", curve: 0),
///   ),
/// )
#let state-machine(states: (), transitions: (), caption: none, initial: none) = {
  figure(
    caption: caption,
    cetz.canvas({
      import cetz: draw

      // Draw states
      for state in states {
        let is-initial = initial == state.id
        draw.circle(
          state.pos,
          radius: 0.6,
          fill: colors.primary.lighten(85%),
          stroke: 2pt + colors.primary,
          name: state.id,
        )

        if is-initial {
          // Initial state marker
          draw.line(
            (state.pos.at(0) - 1.2, state.pos.at(1)),
            (name: state.id, anchor: 180deg),
            stroke: 2pt + colors.primary,
            mark: (end: ">", fill: colors.primary),
          )
        }

        draw.content(
          state.pos,
          text(size: 0.85em, weight: "bold", fill: colors.primary, state.label),
        )
      }

      // Draw transitions
      for trans in transitions {
        let curve-amount = trans.at("curve", default: 0)

        // Get source and target state positions
        let from-state = states.find(s => s.id == trans.from)
        let to-state = states.find(s => s.id == trans.to)

        // Calculate midpoint for label
        let mid-x = (from-state.pos.at(0) + to-state.pos.at(0)) / 2
        let mid-y = (from-state.pos.at(1) + to-state.pos.at(1)) / 2

        if curve-amount == 0 {
          draw.line(
            (name: trans.from),
            (name: trans.to),
            stroke: 1.5pt + colors.secondary,
            mark: (end: ">", fill: colors.secondary),
          )
        } else {
          // Curved transition for self-loops or parallel edges
          draw.bezier(
            (name: trans.from, anchor: trans.at("from-anchor", default: 45deg)),
            (name: trans.to, anchor: trans.at("to-anchor", default: 135deg)),
            (rel: (0, curve-amount), to: (name: trans.from)),
            (rel: (0, curve-amount), to: (name: trans.to)),
            stroke: 1.5pt + colors.secondary,
            mark: (end: ">", fill: colors.secondary),
          )
          // Adjust label position for curved transitions
          mid-y = mid-y + curve-amount * 0.5
        }

        // Transition label at midpoint
        if trans.at("label", default: "") != "" {
          draw.content(
            (mid-x, mid-y),
            anchor: "south",
            padding: 0.1,
            text(
              size: 0.75em,
              fill: colors.text-light,
              box(
                fill: white,
                inset: 0.15em,
                trans.label,
              ),
            ),
          )
        }
      }
    }),
  )
}

/// Timing diagram for showing variable values over time
/// Example:
/// #timing-diagram(
///   signals: (
///     (name: "clk", waves: "P...", period: 1),
///     (name: "mode", values: ("OFF", "STDBY", "HEAT", "STDBY")),
///     (name: "power", values: (0, 500, 2000, 500)),
///   ),
/// )
#let timing-diagram(signals: (), caption: none, time-steps: 8) = {
  let step-width = 0.8
  let row-height = 0.8

  figure(
    cetz.canvas({
      import cetz: draw

      // Draw time axis
      draw.line(
        (0, 0),
        (time-steps * step-width, 0),
        stroke: colors.line,
      )

      for i in range(0, time-steps + 1) {
        draw.line(
          (i * step-width, 0.1),
          (i * step-width, -0.1),
          stroke: colors.line,
        )
        draw.content(
          (i * step-width, -0.3),
          text(size: 0.6em, fill: colors.text-light, str(i)),
        )
      }

      // Draw each signal
      for (idx, signal) in signals.enumerate() {
        let y = -(idx + 1) * row-height - 0.5

        // Signal name
        draw.content(
          (-1.2, y),
          anchor: "east",
          text(size: 0.75em, weight: "bold", fill: colors.primary, signal.name),
        )

        // Signal waveform
        let values = signal.at("values", default: ())

        for (i, val) in values.enumerate() {
          if i < time-steps {
            let x1 = i * step-width
            let x2 = (i + 1) * step-width

            // Draw rectangle for this time step
            draw.rect(
              (x1, y - 0.3),
              (x2, y + 0.3),
              fill: colors.primary.lighten(90%),
              stroke: colors.primary,
            )

            // Value label
            draw.content(
              ((x1 + x2) / 2, y),
              text(size: 0.65em, fill: colors.text, str(val)),
            )
          }
        }
      }
    }),
    caption: caption,
  )
}

/// Control-flow partition visualization
/// Shows how control states partition the abstract state
#let partition-diagram(partitions: (), caption: none) = {
  figure(
    block(
      width: 100%,
      inset: 1em,
      stroke: colors.line,
      radius: 4pt,
    )[
      #grid(
        columns: (1fr, 2fr, 2fr),
        row-gutter: 0.5em,
        column-gutter: 0.8em,

        // Header
        text(weight: "bold", size: 0.85em, "Control State"),
        text(weight: "bold", size: 0.85em, "BDD Formula"),
        text(weight: "bold", size: 0.85em, "Numeric Invariant"),

        // Separator
        line(length: 100%, stroke: colors.line),
        line(length: 100%, stroke: colors.line),
        line(length: 100%, stroke: colors.line),

        // Partitions
        ..partitions
          .map(p => (
            text(size: 0.8em, fill: colors.primary, weight: "bold", p.state),
            text(size: 0.75em, font: fonts.mono, p.formula),
            text(size: 0.75em, font: fonts.mono, p.invariant),
          ))
          .flatten(),
      )
    ],
    caption: caption,
  )
}

/// Truth table visualization
#let truth-table(vars: (), rows: (), caption: none) = {
  figure(
    block(
      inset: 0.8em,
      stroke: colors.line,
      radius: 4pt,
    )[
      #table(
        columns: vars.len() + 1,
        stroke: colors.line,
        fill: (col, row) => if row == 0 {
          colors.primary.lighten(85%)
        } else if col == vars.len() {
          colors.success.lighten(85%)
        },

        // Header
        ..vars.map(v => text(weight: "bold", size: 0.85em, v)),
        text(weight: "bold", size: 0.85em, "f"),

        // Data rows
        ..rows.map(row => row.map(cell => text(size: 0.8em, font: fonts.mono, str(cell)))).flatten(),
      )
    ],
    caption: caption,
  )
}
