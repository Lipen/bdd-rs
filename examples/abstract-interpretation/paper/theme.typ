// Theme and styling for the research paper
// Modern, clean design with emphasis on readability

#import "@preview/numbly:0.1.0"

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
#let theorem(title: none, body) = context {
  theorem-counter.step()
  let number = theorem-counter.display()
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
#let definition(title: none, body) = context {
  definition-counter.step()
  let number = definition-counter.display()
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
#let property(title: none, body) = context {
  property-counter.step()
  let number = property-counter.display()
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
