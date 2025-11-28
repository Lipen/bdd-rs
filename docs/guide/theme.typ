// Theme for BDD Guide
// Modern, vibrant design with clarity and precision

#import "@preview/cetz:0.4.2"
#import "@preview/lovelace:0.3.0"

// ============================================================================
// Color Palette — Formal, academic tones
// ============================================================================

#let colors = (
  // Primary colors — deep, authoritative blues
  primary: rgb("#1e40af"),       // Deep blue
  secondary: rgb("#1e3a5f"),     // Navy blue
  accent: rgb("#0d9488"),        // Teal
  tertiary: rgb("#b45309"),      // Deep amber

  // Text colors
  text: rgb("#1f2937"),          // Near black
  text-light: rgb("#4b5563"),    // Dark gray
  text-muted: rgb("#6b7280"),    // Medium gray

  // Background colors
  bg-main: rgb("#ffffff"),       // Clean white
  bg-subtle: rgb("#f8fafc"),     // Very light gray
  bg-code: rgb("#f1f5f9"),       // Slate gray

  // Semantic colors — balanced
  info: rgb("#0369a1"),          // Deep sky blue
  success: rgb("#047857"),       // Deep emerald
  warning: rgb("#b45309"),       // Deep amber
  error: rgb("#b91c1c"),         // Deep red

  // Box backgrounds — subtle tints
  box-definition: rgb("#eff6ff"),  // Light blue
  box-theorem: rgb("#eef2ff"),     // Light indigo
  box-example: rgb("#ecfdf5"),     // Light emerald
  box-warning: rgb("#fffbeb"),     // Light amber
  box-algorithm: rgb("#fefce8"),   // Light yellow
  box-insight: rgb("#f0f9ff"),     // Pale sky blue

  // Diagram colors (BDD-specific)
  node-decision: rgb("#dbeafe"),   // Light blue
  node-terminal-one: rgb("#d1fae5"),  // Light green
  node-terminal-zero: rgb("#fee2e2"), // Light red
  edge-high: rgb("#1e40af"),       // Deep blue (solid)
  edge-low: rgb("#b91c1c"),        // Deep red (dashed)
  edge-complement: rgb("#1e3a5f"), // Navy

  // UI elements
  line: rgb("#e2e8f0"),           // Slate border
  shadow: rgb("#00000010"),       // Subtle shadow
)

// ============================================================================
// Typography — Classic, scholarly fonts
// ============================================================================

#let fonts = (
  // Main text — elegant serif
  body: "Libertinus Serif",
  // Headings — clean sans-serif
  heading: "Libertinus Sans",
  // Code — clear monospace
  mono: "JetBrains Mono",
  // Math — professional
  math: "New Computer Modern Math",
)

// ============================================================================
// Spacing System
// ============================================================================

#let spacing = (
  tiny: 0.25em,
  small: 0.5em,
  medium: 1em,
  large: 1.5em,
  xlarge: 2em,
  xxlarge: 3em,
  inset-small: 0.8em,
  inset-medium: 1.2em,
  inset-large: 1.8em,
)

// ============================================================================
// Helper Functions
// ============================================================================

#let Green(x) = text(colors.success, x)
#let Red(x) = text(colors.error, x)
#let Blue(x) = text(colors.primary, x)

// ============================================================================
// Mathematical Symbols
// ============================================================================

#let rel(x) = math.class("relation", x)
#let nrel(x) = rel(math.cancel(x))

// BDD-specific symbols
#let ite = $"ite"$                    // If-then-else
#let high = $"high"$                  // High child
#let low = $"low"$                    // Low child
#let mk = $"mk"$                      // Make node

// Text aliases
#let True = Green[`true`]
#let False = Red[`false`]

// ============================================================================
// Helper Symbols
// ============================================================================

#let YES = text(colors.success, weight: "bold")[✓]
#let NO = text(colors.error, weight: "bold")[✗]
#let PARTIAL = text(colors.warning, weight: "bold")[◐]

// ============================================================================
// Document Metadata State
// ============================================================================

#let doc-title = state("doc-title", none)
#let doc-subtitle = state("doc-subtitle", none)
#let doc-authors = state("doc-authors", ())
#let doc-date = state("doc-date", none)

// ============================================================================
// Document Layout Function
// ============================================================================

#let apply-guide-theme(
  title: none,
  subtitle: none,
  authors: (),
  date: none,
  header-title: "Binary Decision Diagrams",
  doc,
) = {
  doc-title.update(title)
  doc-subtitle.update(subtitle)
  doc-authors.update(authors)
  doc-date.update(date)

  // Base text styling
  set text(
    font: fonts.body,
    size: 11pt,
    fill: colors.text,
    lang: "en",
  )

  // Page layout
  set page(
    paper: "a4",
    margin: (top: 3cm, bottom: 3cm, left: 2.5cm, right: 2.5cm),
    numbering: "1",
    number-align: center,
    fill: colors.bg-main,
    header: context {
      if counter(page).get().first() > 1 {
        set text(size: 0.85em, fill: colors.text-muted, font: fonts.heading)
        line(length: 100%, stroke: 0.4pt + colors.line)
        v(-0.4em)
        grid(
          columns: (1fr, 1fr),
          align: (left, right),
          smallcaps(header-title),
          emph[Chapter #counter(heading).display()],
        )
      }
    },
    footer: context {
      set text(size: 0.85em, fill: colors.text-muted)
      set align(center)
      counter(page).display("1")
    },
  )

  // Paragraph settings
  set par(justify: true, first-line-indent: 0em)

  // Heading styles
  set heading(numbering: "1.1")
  show heading: set par(justify: false)

  // Chapter headings (level 1)
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    block(width: 100%, above: spacing.xxlarge, below: spacing.xlarge, sticky: true)[
      #if it.numbering != none {
        text(
          size: 2.5em,
          weight: "regular",
          fill: colors.primary.lighten(40%),
          font: fonts.heading,
        )[Chapter #counter(heading).display(it.numbering)]
        v(spacing.large)
      }
      #text(size: 2em, weight: "bold", fill: colors.primary, font: fonts.heading, it.body)
      #v(spacing.medium)
      #line(length: 35%, stroke: 2.5pt + colors.accent)
    ]
  }

  // Section headings (level 2)
  show heading.where(level: 2): it => {
    block(width: 100%, above: spacing.large, below: spacing.medium, sticky: true)[
      #set text(font: fonts.heading, size: 1.5em, weight: "bold", fill: colors.primary)
      #it
    ]
  }

  // Subsection headings (level 3)
  show heading.where(level: 3): it => {
    block(width: 100%, above: spacing.large, below: spacing.medium, sticky: true)[
      #set text(font: fonts.heading, size: 1.15em, weight: "semibold", fill: colors.accent)
      #it
    ]
  }

  // Minor headings (level 4)
  show heading.where(level: 4): it => {
    v(spacing.small)
    text(font: fonts.heading, size: 1em, weight: "medium", fill: colors.text, style: "italic", it.body + [.])
    h(spacing.small)
  }

  // Code styling
  show raw.where(block: true): it => {
    set text(font: fonts.mono, size: 0.85em, features: ("calt", "liga"))
    block(
      fill: colors.bg-code,
      inset: spacing.inset-medium,
      radius: 6pt,
      width: 100%,
      stroke: 1pt + colors.line,
    )[
      #set par(leading: 0.6em)
      #it
    ]
  }

  show raw.where(block: false): it => {
    h(2pt)
    highlight(
      fill: colors.bg-code,
      radius: 3pt,
      extent: 2pt,
      text(font: fonts.mono, size: 0.9em, fill: colors.primary, it),
    )
    h(2pt)
  }

  // Lists
  set list(marker: ([•], [◦], [–]), indent: 1.2em, body-indent: 0.5em, spacing: 0.7em)
  set enum(numbering: "1.a.i.", indent: 1.2em, body-indent: 0.5em, spacing: 0.7em)

  // Fix emptyset symbol
  show sym.emptyset: set text(font: "Libertinus Sans")

  // Emphasis styling
  show emph: set text(fill: colors.accent)
  show strong: set text(fill: colors.primary)

  // Links
  show link: it => {
    set text(fill: colors.info)
    underline(offset: 2pt, stroke: 0.5pt + colors.info.lighten(50%), it)
  }

  // Figures
  show figure: it => {
    set align(center)
    block(above: spacing.large, below: spacing.large)[
      #it.body
      #v(spacing.small)
      #block(width: 90%)[
        #set text(size: 0.85em, fill: colors.text-light, style: "italic")
        #it.caption
      ]
    ]
  }

  // Tables
  set table(
    stroke: (x, y) => {
      if y == 0 { (bottom: 1.5pt + colors.primary) }
      else { (bottom: 0.5pt + colors.line) }
    },
    fill: (x, y) => {
      if y == 0 { colors.box-definition }
      else if calc.rem(y, 2) == 0 { colors.bg-subtle }
    },
    inset: (x: 0.8em, y: 0.6em),
  )

  // Math equations
  set math.equation(numbering: "(1)", supplement: "Equation")

  show math.equation.where(block: true): it => {
    block(above: spacing.medium, below: spacing.medium, width: 100%)[
      #set align(center)
      #it
    ]
  }

  // Inline fraction style
  show math.equation.where(block: false): set math.frac(style: "horizontal")

  // Part heading
  show figure.where(kind: "part"): it => {
    set par(justify: false)
    set align(center)
    pagebreak(weak: true)
    hide[#heading(bookmarked: true, numbering: none)[#it.caption.body]]
    v(1fr)
    block(width: 100%)[
      #text(
        size: 1.2em,
        weight: "regular",
        fill: colors.text-muted,
        font: fonts.heading,
        tracking: 0.3em,
      )[PART #it.counter.display("I")]
      #v(spacing.medium)
      #line(length: 20%, stroke: 1.5pt + colors.accent)
      #v(spacing.large)
      #text(size: 3em, weight: "bold", fill: colors.primary, font: fonts.heading, it.body)
    ]
    v(1fr)
  }

  doc
}

// ============================================================================
// Title Page
// ============================================================================

#let make-title() = {
  set page(numbering: none)
  context {
    let title = doc-title.get()
    let subtitle = doc-subtitle.get()
    let authors = doc-authors.get()
    let date = doc-date.get()

    align(center)[
      #v(2fr)

      // Decorative element
      #line(length: 40%, stroke: 1pt + colors.accent)
      #v(spacing.large)

      // Title
      #text(size: 2.8em, weight: "bold", fill: colors.primary, font: fonts.heading, title)

      #v(spacing.medium)

      // Subtitle
      #if subtitle != none {
        text(size: 1.3em, fill: colors.text-light, font: fonts.heading, style: "italic", subtitle)
        v(spacing.large)
      }

      #line(length: 40%, stroke: 1pt + colors.accent)

      #v(spacing.xxlarge)

      // Authors
      #for author in authors {
        text(size: 1.1em, fill: colors.text, author)
        v(spacing.small)
      }

      #v(spacing.xlarge)

      // Date
      #if date != none {
        text(size: 1em, fill: colors.text-muted, date)
      }

      #v(2fr)

      // Footer decoration
      #text(size: 0.9em, fill: colors.text-muted, font: fonts.mono)[bdd-rs]
    ]
  }
}

// ============================================================================
// Part Function
// ============================================================================

#let part(title) = figure(
  kind: "part",
  supplement: [Part],
  numbering: "I",
  outlined: false,
  title,
  caption: title,
)

// ============================================================================
// Boxes and Environments
// ============================================================================

#let definition(title: none, body) = block(
  fill: colors.box-definition,
  stroke: (left: 4pt + colors.primary),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.primary, weight: "bold", font: fonts.heading, size: 0.95em)[
    📘 Definition#if title != none [ (#title)]
  ]
  #v(spacing.tiny)
  #body
]

#let theorem(title: none, body) = block(
  fill: colors.box-theorem,
  stroke: (left: 4pt + colors.primary.darken(10%)),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.primary.darken(10%), weight: "bold", font: fonts.heading, size: 0.95em)[
    📐 Theorem#if title != none [ (#title)]
  ]
  #v(spacing.tiny)
  #body
]

#let lemma(title: none, body) = block(
  fill: colors.box-theorem.lighten(20%),
  stroke: (left: 4pt + colors.primary.lighten(30%)),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.primary, weight: "bold", font: fonts.heading, size: 0.95em)[
    Lemma#if title != none [ (#title)]
  ]
  #v(spacing.tiny)
  #body
]

#let proof(body) = block(
  stroke: (left: 2pt + colors.text-muted),
  inset: (left: spacing.inset-medium, y: spacing.small),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(style: "italic", fill: colors.text-light)[Proof.]
  #body
  #h(1fr) $square$
]

#let example-box(title: none, body) = block(
  fill: colors.box-example,
  stroke: (left: 4pt + colors.success),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.success, weight: "bold", font: fonts.heading, size: 0.95em)[
    ✏️ Example#if title != none [ — #title]
  ]
  #v(spacing.tiny)
  #body
]

#let warning-box(title: none, body) = block(
  fill: colors.box-warning,
  stroke: (left: 4pt + colors.warning),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.warning.darken(10%), weight: "bold", font: fonts.heading, size: 0.95em)[
    ⚠️ #if title != none [#title] else [Warning]
  ]
  #v(spacing.tiny)
  #body
]

#let insight-box(body) = block(
  fill: colors.box-insight,
  stroke: (left: 4pt + colors.info),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.info, weight: "bold", font: fonts.heading, size: 0.95em)[
    💡 Key Insight
  ]
  #v(spacing.tiny)
  #body
]

#let info-box(title: none, body) = block(
  fill: colors.box-insight,
  stroke: (left: 4pt + colors.info),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
)[
  #text(fill: colors.info, weight: "bold", font: fonts.heading, size: 0.95em)[
    ℹ️ #if title != none [#title] else [Note]
  ]
  #v(spacing.tiny)
  #body
]

#let algorithm(title: none, body) = block(
  fill: colors.box-algorithm,
  stroke: (left: 4pt + colors.tertiary),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.tertiary.darken(10%), weight: "bold", font: fonts.heading, size: 0.95em)[
    ⚙️ Algorithm#if title != none [: #title]
  ]
  #v(spacing.small)
  #set text(font: fonts.mono, size: 0.9em)
  #body
]

#let implementation-note(body) = block(
  fill: colors.bg-code,
  stroke: (left: 4pt + colors.text-light),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.text, weight: "bold", font: fonts.heading, size: 0.95em)[
    🔧 Implementation Note
  ]
  #v(spacing.tiny)
  #body
]

#let performance-note(body) = block(
  fill: colors.box-warning.lighten(20%),
  stroke: (left: 4pt + colors.warning.lighten(20%)),
  inset: spacing.inset-medium,
  radius: (right: 6pt),
  width: 100%,
  breakable: true,
  sticky: true,
)[
  #text(fill: colors.warning, weight: "bold", font: fonts.heading, size: 0.95em)[
    ⚡ Performance
  ]
  #v(spacing.tiny)
  #body
]

// ============================================================================
// Comparison Table Helper
// ============================================================================

#let comparison-table(cols: 3, ..args) = {
  let items = args.pos()
  if items.len() >= cols {
    table(
      columns: (auto,) * cols,
      align: (left,) + (center,) * (cols - 1),
      // Header row (first `cols` items)
      ..items.slice(0, cols).map(h => strong(h)),
      // Data rows
      ..items.slice(cols)
    )
  }
}

// ============================================================================
// BDD Diagram Helpers (for CeTZ)
// ============================================================================

#let bdd-colors = (
  decision: colors.node-decision,
  terminal-one: colors.node-terminal-one,
  terminal-zero: colors.node-terminal-zero,
  edge-high: colors.edge-high,
  edge-low: colors.edge-low,
)
