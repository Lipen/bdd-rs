// Theme for Abstract Interpretation Tutorial/Guide
// Modern, warm, inviting design optimized for learning

#import "@preview/cetz:0.4.2"
#import "@preview/lovelace:0.3.0"

// ============================================================================
// Color Palette
// ============================================================================

#let colors = (
  // Primary colors - darker and more vibrant
  primary: rgb("#1d4ed8"), // Deep blue
  secondary: rgb("#6d28d9"), // Rich purple
  accent: rgb("#0891b2"), // Cyan
  // Text colors - darker for better readability
  text: rgb("#111827"), // Near black
  text-light: rgb("#4b5563"), // Dark gray
  text-muted: rgb("#6b7280"), // Medium gray
  // Background colors
  bg-main: rgb("#ffffff"), // White
  bg-subtle: rgb("#f9fafb"), // Very light gray
  bg-code: rgb("#f3f4f6"), // Light gray
  // Semantic colors - more vibrant
  info: rgb("#2563eb"), // Vivid blue
  success: rgb("#059669"), // Vivid green
  warning: rgb("#d97706"), // Deep amber
  error: rgb("#dc2626"), // Deep red
  // Box backgrounds - subtle
  box-info: rgb("#eff6ff"), // Light blue
  box-example: rgb("#f0fdf4"), // Light green
  box-warning: rgb("#fffbeb"), // Light amber
  box-theorem: rgb("#faf5ff"), // Light purple
  box-code: rgb("#fef3c7"), // Warm yellow for code examples
  // Diagram colors
  node-bg: rgb("#dbeafe"), // Light blue
  node-border: rgb("#3b82f6"), // Blue
  edge-control: rgb("#7c3aed"), // Purple
  edge-data: rgb("#059669"), // Green
  // UI elements
  line: rgb("#e5e7eb"), // Border gray
  shadow: rgb("#00000020"), // Subtle shadow
  // Code example accent
  code-accent: rgb("#f59e0b"), // Vibrant amber/orange for code examples
)

// ============================================================================
// Typography
// ============================================================================

#let fonts = (
  // Main text - highly readable serif
  body: "Libertinus Serif",
  // Headings - clean sans-serif
  heading: "Liberation Sans",
  // Code - monospace with good ligatures
  mono: "JetBrains Mono",
  // Math - professional
  math: "New Computer Modern Math",
  // Special - for emphasis or callouts
  display: "Playfair Display",
)

// ============================================================================
// Spacing System
// ============================================================================

#let spacing = (
  // Vertical spacing
  tiny: 0.25em,
  small: 0.5em,
  medium: 1em,
  large: 1.5em,
  xlarge: 2em,
  xxlarge: 3em,
  // Horizontal spacing
  gap-small: 0.5em,
  gap-medium: 1em,
  gap-large: 1.5em,
  // Insets
  inset-small: 0.8em,
  inset-medium: 1.2em,
  inset-large: 1.8em,
)

// ============================================================================
// Mathematical Symbols
// ============================================================================

#let rel(x) = math.class("relation", x)
#let nrel(x) = rel(math.cancel(x))

#let ljoin = sym.union.sq       // ⊔ join
#let lmeet = sym.inter.sq       // ⊓ meet
#let widen = rel($nabla$)       // ∇ widening
#let narrow = rel($triangle$)   // △ narrowing
#let lle = $subset.eq.sq$       // ⊑ less-or-equal
#let lge = $supset.eq.sq$       // ⊒ greater-or-equal
#let lbot = $bot$               // ⊥ bottom
#let ltop = $top$               // ⊤ top
#let llb = $bracket.l.stroked$  // ⟦ left semantic bracket
#let rrb = $bracket.r.stroked$  // ⟧ right semantic bracket

// ============================================================================
// Helper Symbols
// ============================================================================

#let YES = text(colors.success, weight: "bold")[✓]
#let NO = text(colors.error, weight: "bold")[✗]
#let MAYBE = text(colors.warning, weight: "bold")[?]

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
  header-title: "Abstract Interpretation with BDDs",
  doc,
) = {
  // Store metadata in state for access by make-title
  doc-title.update(title)
  doc-subtitle.update(subtitle)
  doc-authors.update(authors)
  doc-date.update(date)

  // Base text styling
  set text(
    font: fonts.body,
    size: 12pt,
    fill: colors.text,
    lang: "en",
  )

  // Page layout
  set page(
    paper: "a4",
    margin: (
      top: 2.8cm,
      bottom: 2.8cm,
      left: 2.5cm,
      right: 2.5cm,
    ),
    numbering: "1",
    number-align: center,
    header: context {
      if counter(page).get().first() > 1 {
        set text(size: 0.8em, fill: colors.text-light)
        line(length: 100%, stroke: 0.5pt + colors.line)
        v(-0.5em)
        grid(
          columns: (1fr, 1fr),
          align: (left, right),
          header-title, [Chapter #counter(heading).display()],
        )
      }
    },
  )

  // Paragraph settings
  set par(
    justify: true,
    // leading: 0.7em, // Slightly more leading for readability
    // spacing: 1.3em, // More space between paragraphs
    first-line-indent: 0em,
  )

  // Heading styles
  set heading(numbering: "1.1")

  show heading: set par(justify: false)

  // Chapter headings (level 1)
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    block(
      width: 100%,
      above: spacing.xxlarge,
      below: spacing.large,
      sticky: true,
    )[
      // Chapter number
      #if it.numbering != none {
        text(
          size: 3em,
          weight: "thin",
          fill: colors.primary.lighten(30%),
          font: fonts.heading,
        )[
          Chapter #counter(heading).display(it.numbering)
        ]
        v(spacing.xlarge, weak: true)
      }
      // Chapter title
      #text(
        size: 2.2em,
        weight: "bold",
        fill: colors.primary,
        font: fonts.heading,
        it.body,
      )
    ]
  }

  // Section headings (level 2)
  show heading.where(level: 2): it => {
    block(
      width: 100%,
      above: spacing.large,
      below: spacing.medium,
      sticky: true,
    )[
      #set text(
        font: fonts.heading,
        size: 1.5em,
        weight: "semibold",
        fill: colors.primary,
      )
      #it
    ]
  }

  // Subsection headings (level 3)
  show heading.where(level: 3): it => {
    block(
      width: 100%,
      above: spacing.medium,
      below: spacing.small,
      sticky: true,
    )[
      #set text(
        font: fonts.heading,
        size: 1.2em,
        weight: "semibold",
        fill: colors.secondary,
      )
      #it
    ]
  }

  // Minor headings (level 4)
  show heading.where(level: 4): it => {
    v(spacing.small)
    text(
      font: fonts.heading,
      size: 1.05em,
      weight: "medium",
      fill: colors.text,
      style: "italic",
      it.body + [.],
    )
    h(spacing.small)
  }

  // Code styling
  show raw.where(block: true): it => {
    set text(
      font: fonts.mono,
      size: 0.8em,
      features: ("calt", "liga"),
    )
    block(
      fill: colors.bg-code,
      inset: spacing.inset-medium,
      radius: 6pt,
      width: 100%,
      stroke: 0.5pt + colors.line,
    )[
      #set par(leading: 0.6em)
      #it
    ]
  }

  show raw.where(block: false): it => {
    box(
      fill: colors.bg-code,
      outset: (x: 3pt, y: 2pt),
      radius: 3pt,
    )[
      #text(
        font: fonts.mono,
        size: 0.92em,
        fill: colors.primary,
        it,
      )
    ]
  }

  // Lists
  set list(
    marker: ([•], [◦], [▸]),
    indent: 1.2em,
    body-indent: 0.5em,
    spacing: 0.8em,
  )

  set enum(
    numbering: "1.a.i.",
    indent: 1.2em,
    body-indent: 0.5em,
    spacing: 0.8em,
  )

  // Fix emptyset symbol
  show sym.emptyset: set text(font: "Libertinus Sans")

  // Colored emphasis
  show emph: set text(fill: colors.accent)

  // Colored bold text
  show strong: set text(fill: colors.primary)

  // Links
  show link: it => {
    set text(fill: colors.accent)
    it
  }

  // Figures
  show figure: it => {
    set align(center)
    block(
      above: spacing.large,
      below: spacing.large,
    )[
      #it.body
      #v(spacing.small)
      // Caption
      #block(
        width: 90%,
      )[
        #set text(
          size: 0.8em,
          fill: colors.text-light,
          style: "italic",
        )
        *Figure #it.counter.display(it.numbering):* #it.caption
      ]
    ]
  }

  // Tables
  set table(
    stroke: (x, y) => {
      if y == 0 {
        (bottom: 1.5pt + colors.primary)
      } else {
        (bottom: 0.5pt + colors.line)
      }
    },
    fill: (x, y) => {
      if y == 0 {
        colors.box-info
      } else if calc.rem(y, 2) == 0 {
        colors.bg-subtle
      }
    },
    inset: (x: 0.8em, y: 0.6em),
  )

  // Math equations
  set math.equation(
    numbering: "(1)",
    supplement: "Equation",
  )

  show math.equation.where(block: true): it => {
    block(
      above: spacing.medium,
      below: spacing.medium,
      width: 100%,
    )[
      #set align(center)
      #it
    ]
  }

  // Inline fraction
  show math.equation.where(block: false): set math.frac(style: "horizontal")

  // Part heading
  // Note: setup after 'show figure'
  show figure.where(kind: "part"): it => {
    set par(justify: false)
    set align(left)
    pagebreak(weak: true)
    // Hidden heading for TOC/bookmark
    hide[
      #heading(bookmarked: true, numbering: none)[
        #it.supplement #it.counter.display(it.numbering): #it.body
      ]
    ]
    block(
      width: 100%,
      above: spacing.xxlarge,
      below: spacing.large,
      sticky: true,
    )[
      // Part number
      #text(
        size: 3em,
        weight: "bold",
        fill: colors.primary.lighten(30%),
        font: fonts.heading,
        tracking: 0.1em,
      )[
        #it.supplement #it.counter.display(it.numbering)
      ]
      #v(spacing.xlarge, weak: true)
      // Part title
      #text(
        size: 2.2em,
        weight: "bold",
        fill: colors.primary,
        font: fonts.heading,
        tracking: 0.05em,
        it.body,
      )
    ]
  }

  // Bibliography
  set bibliography(
    title: "References and Further Reading",
    style: "ieee",
  )

  // Show some abbreviations in italic
  show "i.e.": set text(style: "italic")
  show "e.g.": set text(style: "italic")
  show "etc.": set text(style: "italic")
  show "et al.": set text(style: "italic")

  // Render the document
  doc
}

// ============================================================================
// Special Boxes for Pedagogy
// ============================================================================

// Information box
#let info-box(title: "Note", body) = {
  block(
    stroke: (left: 2.5pt + colors.info),
    inset: (left: 1em, rest: 0.8em),
    width: 100%,
    breakable: true,
  )[
    #text(
      font: fonts.heading,
      weight: "semibold",
      fill: colors.info,
      size: 0.9em,
      title,
    )
    #[ ]
    #body
  ]
}

// Example box
#let example-box(title: "Example", number: none, body) = {
  let display-title = if number != none {
    [Example #number: #title]
  } else {
    title
  }

  block(
    fill: colors.box-example,
    stroke: (left: 2.5pt + colors.success),
    inset: (left: 1em, rest: 0.8em),
    width: 100%,
    breakable: true,
  )[
    #text(
      font: fonts.heading,
      weight: "semibold",
      fill: colors.success,
      size: 0.9em,
      display-title,
    )
    #v(spacing.small)
    #body
  ]
}

// Warning/caution box
#let warning-box(title: "Caution", body) = {
  block(
    fill: colors.box-warning,
    stroke: (left: 2.5pt + colors.warning),
    inset: (left: 1em, rest: 0.8em),
    width: 100%,
    breakable: true,
  )[
    #text(
      font: fonts.heading,
      weight: "semibold",
      fill: colors.warning,
      size: 0.9em,
      title,
    )
    #[ ]
    #body
  ]
}

// Exercise box
#let exercise-box(number: none, difficulty: none, body) = {
  let display-title = if number != none {
    [Exercise #number]
  } else {
    [Exercise]
  }

  block(
    fill: colors.box-theorem,
    stroke: (left: 3pt + colors.secondary),
    inset: spacing.inset-medium,
    radius: 4pt,
    width: 100%,
    breakable: true,
  )[
    #grid(
      columns: (auto, 1fr, auto),
      column-gutter: 0.8em,
      align: (center + horizon, left, right + horizon),
      // Icon
      text(
        size: 1.5em,
        fill: colors.secondary,
        "✏️",
      ),
      // Title
      text(
        font: fonts.heading,
        weight: "semibold",
        fill: colors.secondary,
        size: 0.95em,
        display-title,
      ),
      // Difficulty
      if difficulty != none {
        text(
          size: 0.85em,
          fill: colors.text-muted,
          style: "italic",
          difficulty,
        )
      },
    )
    #v(spacing.small)
    #body
  ]
}

// Key insight box
#let insight-box(body) = {
  block(
    stroke: (left: 3pt + colors.accent),
    inset: (left: 1em, rest: 0.8em),
    width: 100%,
  )[
    #text(
      font: fonts.heading,
      weight: "bold",
      fill: colors.accent,
      size: 0.9em,
      [Key Insight],
    )
    #[ ]
    #body
  ]
}

// Historical note box
#let historical-note(
  person: none,
  year: none,
  title: none,
  image-path: none, // Placeholder for now
  body,
) = {
  block(
    fill: colors.bg-subtle,
    stroke: 1pt + colors.text-muted,
    radius: 3pt,
    inset: 1em,
    width: 100%,
    breakable: true,
  )[
    // Header with person and year
    #if person != none or year != none {
      grid(
        columns: (auto, 1fr),
        column-gutter: 0.5em,
        if image-path != none {
          // Placeholder for image
          box(
            width: 4em,
            height: 4em,
            fill: colors.line,
            radius: 2pt,
            align(center + horizon)[
              text(size: 0.7em, fill: colors.text-muted)[Image]
            ],
          )
        },
        {
          if person != none {
            text(
              font: fonts.heading,
              weight: "bold",
              size: 0.95em,
              fill: colors.text,
              person,
            )
            if year != none {
              [ (#year)]
            }
            linebreak()
          }
          if title != none {
            text(
              style: "italic",
              size: 0.85em,
              fill: colors.text-light,
              title,
            )
          }
        },
      )
      v(spacing.small)
    }

    // Body text
    #body
  ]
}

// ============================================================================
// Formal Math Environments
// ============================================================================

// Counters for numbered environments
#let definition-counter = counter("definition")
#let theorem-counter = counter("theorem")
#let lemma-counter = counter("lemma")
#let proposition-counter = counter("proposition")
#let algorithm-counter = counter("algorithm")

#let definition(title: none, body) = {
  definition-counter.step()
  let number = context definition-counter.display()
  let display-title = if title != none {
    [Definition #number (#title)]
  } else {
    [Definition #number]
  }

  block(
    fill: colors.box-info,
    stroke: (left: 3pt + colors.primary),
    inset: spacing.inset-medium,
    radius: 4pt,
    width: 100%,
    breakable: false,
  )[
    #text(
      font: fonts.heading,
      weight: "bold",
      fill: colors.primary,
      size: 0.95em,
      display-title,
    )
    #h(spacing.small)
    #body
  ]
}

#let theorem(title: none, body) = {
  theorem-counter.step()
  let number = context theorem-counter.display()
  let display-title = if title != none {
    [Theorem #number (#title)]
  } else {
    [Theorem #number]
  }

  block(
    fill: colors.box-theorem,
    stroke: (left: 3pt + colors.secondary),
    inset: spacing.inset-medium,
    radius: 4pt,
    width: 100%,
    breakable: false,
  )[
    #text(
      font: fonts.heading,
      weight: "bold",
      fill: colors.secondary,
      size: 0.95em,
      display-title,
    )
    #h(spacing.small)
    #body
  ]
}

#let proof(body) = {
  block(
    stroke: (left: 2pt + colors.text-light),
    inset: (left: spacing.inset-medium, rest: spacing.inset-small),
    width: 100%,
    breakable: true,
  )[
    #text(
      font: fonts.heading,
      weight: "semibold",
      style: "italic",
      fill: colors.text-light,
      size: 0.9em,
      [Proof.],
    )
    #h(spacing.small)
    #body
    #h(1fr)
    // QED symbol
    #box(
      baseline: 0.2em,
      square(
        size: 0.65em,
        fill: colors.text-light,
      ),
    )
  ]
}

// Algorithm environment with lovelace integration
#let algorithm(
  title: none,
  hooks: 0.5em,
  booktabs: false,
  numbered-title: [],
  body,
) = {
  algorithm-counter.step()
  let number = context algorithm-counter.display()
  let display-title = if title != none {
    [Algorithm #number: #title]
  } else {
    [Algorithm #number]
  }

  block(
    fill: rgb("#fefce8"), // Subtle yellow background
    stroke: (left: 3pt + colors.warning),
    inset: spacing.inset-medium,
    radius: 4pt,
    width: 100%,
    breakable: true,
  )[
    #text(
      font: fonts.heading,
      weight: "bold",
      fill: colors.warning,
      size: 0.95em,
      display-title,
    )
    // #v(spacing.small, weak: true)
    #v(0pt, weak: true)
    #v(-1em)
    #lovelace.pseudocode-list(
      hooks: hooks,
      booktabs: booktabs,
      numbered-title: numbered-title,
      body,
    )
    #v(-1em)
  ]
}

// ============================================================================
// Margin Notes and Callouts
// ============================================================================

#let margin-note(body) = {
  place(
    right + horizon,
    dx: 2.5cm,
  )[
    #box(
      width: 4cm,
    )[
      #set text(size: 0.7em, fill: colors.text-light)
      #set par(justify: false, leading: 0.6em)
      #body
    ]
  ]
}

// ============================================================================
// Title Page Helpers
// ============================================================================

#let make-title() = context {
  let title = doc-title.get()
  let subtitle = doc-subtitle.get()
  let authors = doc-authors.get()
  let date = doc-date.get()

  set align(center)

  v(3cm)

  // Main title
  if title != none {
    text(
      size: 2.8em,
      weight: "bold",
      fill: colors.primary,
      font: fonts.heading,
      title,
    )
  }

  v(spacing.medium)

  // Subtitle
  if subtitle != none {
    text(
      size: 1.5em,
      weight: "regular",
      fill: colors.secondary,
      font: fonts.heading,
      subtitle,
    )
    v(spacing.large)
  }

  v(2cm)

  // Authors
  if authors != () {
    text(
      size: 1.2em,
      fill: colors.text,
      font: fonts.body,
      authors.join(", "),
    )
    v(spacing.medium)
  }

  // Date
  if date != none {
    text(
      size: 1em,
      fill: colors.text-light,
      date,
    )
  }

  v(1fr)

  pagebreak()
}

// ============================================================================
// Part Title Page
// ============================================================================

#let part(title) = {
  figure(
    kind: "part",
    supplement: "Part",
    numbering: "I",
    title,
  )
}

// ============================================================================
// Chapter Summaries
// ============================================================================

#let chapter-summary(title: "Chapter Summary", body) = {
  block(
    fill: colors.bg-subtle,
    stroke: 1pt + colors.line,
    inset: spacing.inset-large,
    radius: 6pt,
    width: 100%,
  )[
    #text(
      font: fonts.heading,
      weight: "bold",
      size: 1.1em,
      fill: colors.primary,
      title,
    )

    #set list(spacing: spacing.medium, indent: 0pt)
    #body
  ]
}

// ============================================================================
// Reading Path Indicators
// ============================================================================

#let reading-path(path: "essential") = {
  let (icon, color, label) = if path == "essential" {
    ("⭐", colors.warning, "Essential")
  } else if path == "beginner" {
    ("🌱", colors.success, "Beginner-Friendly")
  } else if path == "advanced" {
    ("🔬", colors.secondary, "Advanced")
  } else if path == "implementation" {
    ("💻", colors.info, "Implementation Focus")
  } else {
    ("📖", colors.text-light, "General")
  }

  box(
    inset: (x: 0.1em),
    baseline: 0.1em,
    box(
      fill: color.lighten(85%),
      stroke: 1pt + color,
      radius: 4pt,
      inset: (x: 0.5em, bottom: 0.4em, top: 0.2em),
    )[
      #text(
        size: 0.85em,
        fill: color,
        weight: "medium",
        [#icon #label],
      )
    ],
  )
}

// ============================================================================
// Code Example References
// ============================================================================

// Base path for code examples in the repository
#let code-examples-base = "https://github.com/Lipen/bdd-rs/tree/master/examples/abstract-interpretation/guide/code-examples"

// Link to a complete runnable code example
#let code-example(
  topic,
  file,
  description: none,
  icon: true,
) = {
  let url = code-examples-base + "/" + topic + "/" + file
  let display = if description != none {
    description
  } else {
    file
  }

  box(
    baseline: 0.3em,
    inset: (x: 0.3em, y: 0.3em),
    fill: colors.bg-code,
    radius: 3pt,
    stroke: 0.5pt + colors.line,
  )[
    #link(url)[
      #if icon {
        box(
          baseline: 0.1em,
          text(size: 0.9em, fill: colors.primary)[📄],
        )
        h(0.2em)
      }
      #text(
        size: 0.9em,
        fill: colors.accent,
        font: fonts.mono,
        display,
      )
    ]
  ]
}

// Reference to run a specific example
#let run-example(example-name) = {
  box(
    baseline: 0.3em,
    inset: (x: 0.5em, y: 0.3em),
    fill: colors.box-info,
    radius: 3pt,
    stroke: 0.5pt + colors.info,
  )[
    #text(
      size: 0.85em,
      fill: colors.info,
      font: fonts.mono,
    )[
      `cargo run --example` #raw(example-name)
    ]
  ]
}

// Inline mention of code location for quick reference
#let code-ref(topic, file) = {
  text(
    size: 0.9em,
    font: fonts.mono,
    fill: colors.text-light,
  )[
    code-examples/#topic/#file
  ]
}

// Full example reference block with description and run instructions
#let example-reference(
  topic,
  file,
  example-name,
  description,
) = {
  block(
    fill: colors.box-code,
    stroke: (left: 4pt + colors.code-accent, rest: 1pt + colors.code-accent.lighten(60%)),
    inset: spacing.inset-medium,
    radius: 6pt,
    width: 100%,
    breakable: false,
  )[
    #grid(
      columns: (auto, 1fr),
      column-gutter: 0.8em,
      row-gutter: 0.5em,
      // Icon with circular background
      box(
        fill: colors.code-accent.lighten(80%),
        stroke: 1.5pt + colors.code-accent,
        radius: 50%,
        inset: 0.3em,
      )[
        #text(size: 1.2em)[💻]
      ],
      // Title
      text(
        font: fonts.heading,
        weight: "bold",
        size: 1em,
        fill: colors.code-accent.darken(20%),
      )[Hands-On Example],
      // Empty cell
      [],
      // Content
      {
        text(size: 0.92em, style: "normal")[#description]
        v(spacing.small)

        // Compact layout for source and run command
        box(
          fill: white.darken(3%),
          stroke: 0.5pt + colors.line,
          radius: 4pt,
          inset: 0.6em,
          width: 100%,
        )[
          #grid(
            columns: (auto, 1fr),
            column-gutter: 1.2em,
            row-gutter: 0.5em,
            // Source label and path
            text(weight: "semibold", size: 0.83em, fill: colors.code-accent.darken(15%))[📄 Source:],
            code-example(topic, file, icon: false),
            // Run label and command
            text(weight: "semibold", size: 0.83em, fill: colors.code-accent.darken(15%))[▶ Run:],
            run-example(example-name),
          )
        ]
      },
    )
  ]
}

// Quick inline reference combining code location and example name
#let inline-example(topic, file, example-name) = {
  code-example(topic, file, icon: false)
  [ (]
  run-example(example-name)
  [)]
}

