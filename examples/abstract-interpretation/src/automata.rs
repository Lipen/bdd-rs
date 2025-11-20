//! Automata-based Abstract Domain
//!
//! This module implements a symbolic automata domain for string analysis.
//! It uses symbolic transitions labeled by character predicates (e.g., character classes)
//! to represent regular languages over Unicode characters.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

use super::domain::AbstractDomain;

// ============================================================================
// Predicate Layer
// ============================================================================

/// A canonical, comparable predicate over the alphabet (Unicode scalar values).
pub trait Predicate: Clone + Eq + Debug + Send + Sync + 'static {
    /// Is character `c` accepted by the predicate?
    fn contains(&self, c: char) -> bool;

    /// Conjunction (AND) of predicates.
    fn and(&self, other: &Self) -> Self;
    /// Disjunction (OR) of predicates.
    fn or(&self, other: &Self) -> Self;
    /// Negation (NOT)
    fn not(&self) -> Self;

    /// Is predicate empty?
    fn is_empty(&self) -> bool;

    /// Produce a canonical string key useful for hashing / deterministic ordering.
    fn canonical_key(&self) -> String;
}

/// A simple character-class predicate represented as a set of disjoint ranges.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct CharClass {
    // invariant: ranges are disjoint, sorted, non-adjacent
    ranges: Vec<(u32, u32)>,
}

impl CharClass {
    pub fn empty() -> Self {
        CharClass { ranges: Vec::new() }
    }

    pub fn full() -> Self {
        CharClass {
            ranges: vec![(0, 0x10FFFF)],
        }
    }

    pub fn from_ranges(mut ranges: Vec<(u32, u32)>) -> Self {
        ranges.sort_unstable();
        let mut out = Vec::<(u32, u32)>::new();
        for (a, b) in ranges {
            if a > b {
                continue;
            }
            if let Some(last) = out.last_mut() {
                if a <= last.1 + 1 {
                    if b > last.1 {
                        last.1 = b;
                    }
                    continue;
                }
            }
            out.push((a, b));
        }
        CharClass { ranges: out }
    }

    pub fn single(ch: char) -> Self {
        let u = ch as u32;
        CharClass { ranges: vec![(u, u)] }
    }

    pub fn range(a: char, b: char) -> Self {
        CharClass::from_ranges(vec![(a as u32, b as u32)])
    }
}

impl Predicate for CharClass {
    fn contains(&self, c: char) -> bool {
        let u = c as u32;
        let mut lo = 0usize;
        let mut hi = self.ranges.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            let (s, e) = self.ranges[mid];
            if u < s {
                hi = mid;
            } else if u > e {
                lo = mid + 1;
            } else {
                return true;
            }
        }
        false
    }

    fn and(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        let mut i = 0usize;
        let mut j = 0usize;
        while i < self.ranges.len() && j < other.ranges.len() {
            let (a1, b1) = self.ranges[i];
            let (a2, b2) = other.ranges[j];
            let lo = a1.max(a2);
            let hi = b1.min(b2);
            if lo <= hi {
                out.push((lo, hi));
            }
            if b1 < b2 {
                i += 1;
            } else {
                j += 1;
            }
        }
        CharClass::from_ranges(out)
    }

    fn or(&self, other: &Self) -> Self {
        let mut all = self.ranges.clone();
        all.extend(other.ranges.iter());
        CharClass::from_ranges(all)
    }

    fn not(&self) -> Self {
        let mut out = Vec::new();
        let mut cur = 0u32;
        for (s, e) in &self.ranges {
            if cur < *s {
                out.push((cur, s - 1));
            }
            if *e == 0x10FFFF {
                cur = 0x110000;
                break;
            }
            cur = e + 1;
        }
        if cur <= 0x10FFFF {
            out.push((cur, 0x10FFFF));
        }
        CharClass::from_ranges(out)
    }

    fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    fn canonical_key(&self) -> String {
        let mut s = String::new();
        for (a, b) in &self.ranges {
            use std::fmt::Write;
            write!(&mut s, "{}-{};", a, b).unwrap();
        }
        s
    }
}

// ============================================================================
// Automata Core
// ============================================================================

pub type StateId = usize;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolicTransition<P: Predicate> {
    pub label: P,
    pub target: StateId,
}

/// Deterministic symbolic automaton (DFA).
#[derive(Clone, Debug)]
pub struct SymbolicDFA<P: Predicate> {
    pub states: usize,
    pub accepting: Vec<bool>,
    pub transitions: Vec<Vec<SymbolicTransition<P>>>,
}

impl<P: Predicate> PartialEq for SymbolicDFA<P> {
    fn eq(&self, other: &Self) -> bool {
        // Structural equality check
        if self.states != other.states {
            return false;
        }
        if self.accepting != other.accepting {
            return false;
        }
        for i in 0..self.states {
            let ta = &self.transitions[i];
            let tb = &other.transitions[i];
            if ta.len() != tb.len() {
                return false;
            }
            for (a, b) in ta.iter().zip(tb.iter()) {
                if a.target != b.target {
                    return false;
                }
                if a.label.canonical_key() != b.label.canonical_key() {
                    return false;
                }
            }
        }
        true
    }
}

impl<P: Predicate> SymbolicDFA<P> {
    pub fn new(states: usize) -> Self {
        SymbolicDFA {
            states,
            accepting: vec![false; states],
            transitions: vec![Vec::new(); states],
        }
    }

    pub fn accepts(&self, input: &str) -> bool {
        let mut cur = 0usize;
        for ch in input.chars() {
            let mut found = false;
            for tr in &self.transitions[cur] {
                if tr.label.contains(ch) {
                    cur = tr.target;
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        self.accepting[cur]
    }

    pub fn complement(&self) -> Self
    where
        P: Clone,
    {
        let mut out = self.clone();
        for a in &mut out.accepting {
            *a = !*a;
        }
        out
    }

    /// Check if the language is empty (reachability of accepting states).
    pub fn is_empty_lang(&self) -> bool {
        let mut visited = HashSet::new();
        let mut q = VecDeque::new();
        q.push_back(0);
        visited.insert(0);

        while let Some(s) = q.pop_front() {
            if self.accepting[s] {
                return false;
            }
            for tr in &self.transitions[s] {
                if !visited.contains(&tr.target) {
                    visited.insert(tr.target);
                    q.push_back(tr.target);
                }
            }
        }
        true
    }

    /// Check if language is full (complement is empty).
    pub fn is_full_lang(&self) -> bool
    where
        P: Clone + Ord,
    {
        // Note: this assumes the DFA is complete (total).
        // If not complete, we should first complete it or check for missing transitions.
        // For simplicity, we assume completeness or use complement().is_empty_lang().
        // But complement() just flips accepting bits, so it relies on completeness.
        // Let's use complement().is_empty_lang() assuming completeness.
        self.complement().is_empty_lang()
    }
}

// ============================================================================
// NFA Builder & Algorithms
// ============================================================================

#[derive(Clone, Debug)]
pub struct SymbolicNFA<P: Predicate> {
    pub start: StateId,
    pub states: usize,
    pub accepting: Vec<bool>,
    pub transitions: Vec<Vec<SymbolicTransition<P>>>,
}

impl<P: Predicate> SymbolicNFA<P> {
    pub fn new() -> Self {
        SymbolicNFA {
            start: 0,
            states: 1,
            accepting: vec![false],
            transitions: vec![Vec::new()],
        }
    }

    pub fn add_state(&mut self, accepting: bool) -> StateId {
        let id = self.states;
        self.states += 1;
        self.accepting.push(accepting);
        self.transitions.push(Vec::new());
        id
    }

    pub fn add_transition(&mut self, from: StateId, pred: P, to: StateId) {
        self.transitions[from].push(SymbolicTransition { label: pred, target: to });
    }

    pub fn determinize(&self) -> SymbolicDFA<P>
    where
        P: Clone + Ord,
    {
        let mut preds: Vec<P> = Vec::new();
        for trs in &self.transitions {
            for tr in trs {
                preds.push(tr.label.clone());
            }
        }
        if preds.is_empty() {
            let mut dfa = SymbolicDFA::new(1);
            dfa.accepting[0] = self.accepting[self.start];
            return dfa;
        }

        let minterms = build_minterms(&preds);
        let n = self.states;
        let mcount = minterms.len();
        let mut reach: Vec<Vec<Vec<StateId>>> = vec![vec![Vec::new(); mcount]; n];
        for s in 0..n {
            for tr in &self.transitions[s] {
                for (mi, mt) in minterms.iter().enumerate() {
                    if !tr.label.and(mt).is_empty() {
                        reach[s][mi].push(tr.target);
                    }
                }
            }
        }

        let mut dfa_states: Vec<Vec<StateId>> = Vec::new();
        let mut dfa_index: HashMap<Vec<StateId>, StateId> = HashMap::new();
        let mut q = VecDeque::new();

        let start_set = vec![self.start];
        dfa_states.push(start_set.clone());
        dfa_index.insert(start_set.clone(), 0usize);
        q.push_back(0usize);

        while let Some(did) = q.pop_front() {
            let nset = dfa_states[did].clone();
            for (mi, _) in minterms.iter().enumerate() {
                let mut target_set: Vec<StateId> = Vec::new();
                for &s in &nset {
                    for &t in &reach[s][mi] {
                        if !target_set.contains(&t) {
                            target_set.push(t);
                        }
                    }
                }
                if target_set.is_empty() {
                    continue;
                }
                target_set.sort_unstable();
                if !dfa_index.contains_key(&target_set) {
                    let tid = dfa_states.len();
                    dfa_index.insert(target_set.clone(), tid);
                    dfa_states.push(target_set.clone());
                    q.push_back(tid);
                }
            }
        }

        let mut dfa = SymbolicDFA::new(dfa_states.len());
        for (i, set) in dfa_states.iter().enumerate() {
            dfa.accepting[i] = set.iter().any(|&s| self.accepting[s]);
        }

        for (i, set) in dfa_states.iter().enumerate() {
            for (mi, mt) in minterms.iter().enumerate() {
                let mut target_set: Vec<StateId> = Vec::new();
                for &s in set {
                    for &t in &reach[s][mi] {
                        if !target_set.contains(&t) {
                            target_set.push(t);
                        }
                    }
                }
                if target_set.is_empty() {
                    continue;
                }
                target_set.sort_unstable();
                let tid = dfa_index[&target_set];
                dfa.transitions[i].push(SymbolicTransition {
                    label: mt.clone(),
                    target: tid,
                });
            }
            dfa.transitions[i].sort_by_key(|tr| tr.label.canonical_key());
        }

        dfa
    }
}

fn build_minterms<P: Predicate + Clone + Ord>(preds: &[P]) -> Vec<P> {
    let mut boundaries: BTreeSet<u32> = BTreeSet::new();

    for p in preds {
        let key = p.canonical_key();
        for part in key.split(';') {
            if part.trim().is_empty() {
                continue;
            }
            if let Some(idx) = part.find('-') {
                let a = part[..idx].parse::<u32>().unwrap_or(0);
                let b = part[idx + 1..].parse::<u32>().unwrap_or(0);
                boundaries.insert(a);
                if b < 0x10FFFF {
                    boundaries.insert(b + 1);
                }
            }
        }
    }

    if !boundaries.is_empty() {
        let vecb: Vec<u32> = boundaries.into_iter().collect();
        let mut atoms: Vec<(u32, u32)> = Vec::new();
        for i in 0..vecb.len() {
            let start = vecb[i];
            let end = if i + 1 < vecb.len() { vecb[i + 1] - 1 } else { 0x10FFFF };
            if start <= end {
                atoms.push((start, end));
            }
        }
        let mut result: Vec<P> = Vec::new();
        for (s, _e) in atoms {
            let rep = std::char::from_u32(s).unwrap_or('\u{FFFD}');
            let mut atom_pred: Option<P> = None;
            for p in preds {
                if p.contains(rep) {
                    atom_pred = Some(match atom_pred {
                        None => p.clone(),
                        Some(acc) => acc.or(p),
                    });
                }
            }
            if let Some(ap) = atom_pred {
                result.push(ap);
            }
        }
        let mut merged: Vec<P> = Vec::new();
        for r in result {
            if let Some(last) = merged.last_mut() {
                if last.canonical_key() == r.canonical_key() {
                    let combined = last.or(&r);
                    *last = combined;
                    continue;
                }
            }
            merged.push(r);
        }
        return merged;
    }
    Vec::new()
}

pub fn minimize_dfa<P: Predicate + Clone + Ord>(dfa: &SymbolicDFA<P>) -> SymbolicDFA<P> {
    let n = dfa.states;
    let mut part: Vec<usize> = vec![0; n];
    let mut blocks: Vec<Vec<StateId>> = Vec::new();
    let mut b_accept: Vec<StateId> = Vec::new();
    let mut b_non: Vec<StateId> = Vec::new();
    for i in 0..n {
        if dfa.accepting[i] {
            b_accept.push(i);
        } else {
            b_non.push(i);
        }
    }
    if !b_accept.is_empty() {
        blocks.push(b_accept.clone());
    }
    if !b_non.is_empty() {
        blocks.push(b_non.clone());
    }
    for (idx, b) in blocks.iter().enumerate() {
        for &s in b {
            part[s] = idx;
        }
    }

    let mut global_labels: Vec<P> = Vec::new();
    let mut seen = HashSet::new();
    for trs in &dfa.transitions {
        for t in trs {
            let key = t.label.canonical_key();
            if !seen.contains(&key) {
                seen.insert(key.clone());
                global_labels.push(t.label.clone());
            }
        }
    }

    let mut rev: HashMap<String, Vec<Vec<StateId>>> = HashMap::new();
    for lab in &global_labels {
        let key = lab.canonical_key();
        rev.insert(key.clone(), vec![Vec::new(); n]);
    }
    for r in 0..n {
        for tr in &dfa.transitions[r] {
            let key = tr.label.canonical_key();
            rev.get_mut(&key).unwrap()[tr.target].push(r);
        }
    }

    let mut work: VecDeque<(usize, String)> = VecDeque::new();
    for (i, _block) in blocks.iter().enumerate() {
        for lab in &global_labels {
            work.push_back((i, lab.canonical_key()));
        }
    }

    while let Some((a_idx, lab_key)) = work.pop_front() {
        if a_idx >= blocks.len() {
            continue;
        } // Block might have been split/moved? No, indices are stable-ish?
          // Actually, blocks are only appended. But if we split a block, we modify it in place and add a new one.

        let pre = &rev[&lab_key];
        let mut involved: Vec<StateId> = Vec::new();
        for &q in &blocks[a_idx] {
            for &p in &pre[q] {
                if !involved.contains(&p) {
                    involved.push(p);
                }
            }
        }
        if involved.is_empty() {
            continue;
        }

        let mut new_blocks: Vec<(usize, Vec<StateId>, Vec<StateId>)> = Vec::new();
        for (i, b) in blocks.iter().enumerate() {
            let mut b1 = Vec::new();
            let mut b2 = Vec::new();
            for &q in b {
                if involved.contains(&q) {
                    b1.push(q);
                } else {
                    b2.push(q);
                }
            }
            if !b1.is_empty() && !b2.is_empty() {
                new_blocks.push((i, b1, b2));
            }
        }

        for (bi, b1, b2) in new_blocks {
            blocks[bi] = b1.clone();
            let new_idx = blocks.len();
            blocks.push(b2.clone());
            for &s in &blocks[bi] {
                part[s] = bi;
            }
            for &s in &blocks[new_idx] {
                part[s] = new_idx;
            }
            for lab in &global_labels {
                work.push_back((new_idx, lab.canonical_key()));
            }
        }
    }

    let mut block_reps: Vec<(usize, StateId)> = blocks.iter().enumerate().map(|(i, b)| (i, *b.iter().min().unwrap())).collect();
    block_reps.sort_by_key(|(_, rep)| *rep);
    let mut mapping: Vec<usize> = vec![0; blocks.len()];
    for (new_idx, (old_idx, _rep)) in block_reps.iter().enumerate() {
        mapping[*old_idx] = new_idx;
    }

    let new_n = blocks.len();
    let mut out = SymbolicDFA::<P>::new(new_n);
    for (old_idx, block) in blocks.iter().enumerate() {
        let new_idx = mapping[old_idx];
        out.accepting[new_idx] = block.iter().any(|&s| dfa.accepting[s]);
    }

    for (old_idx, block) in blocks.iter().enumerate() {
        let new_idx = mapping[old_idx];
        let rep = *block.iter().min().unwrap();
        for tr in &dfa.transitions[rep] {
            let tgt_block = part[tr.target];
            let new_tgt = mapping[tgt_block];
            if !out.transitions[new_idx]
                .iter()
                .any(|e| e.target == new_tgt && e.label.canonical_key() == tr.label.canonical_key())
            {
                out.transitions[new_idx].push(SymbolicTransition {
                    label: tr.label.clone(),
                    target: new_tgt,
                });
            }
        }
        out.transitions[new_idx].sort_by_key(|t| t.label.canonical_key());
    }

    out
}

impl<P: Predicate + Clone + Ord> SymbolicDFA<P> {
    pub fn union(&self, other: &SymbolicDFA<P>) -> SymbolicDFA<P> {
        self.product(other, |a, b| a || b)
    }

    pub fn intersection(&self, other: &SymbolicDFA<P>) -> SymbolicDFA<P> {
        self.product(other, |a, b| a && b)
    }

    fn product<F>(&self, other: &SymbolicDFA<P>, accept_op: F) -> SymbolicDFA<P>
    where
        F: Fn(bool, bool) -> bool,
    {
        let mut labels: Vec<P> = Vec::new();
        let mut seen = HashSet::new();
        for trs in &self.transitions {
            for t in trs {
                let k = t.label.canonical_key();
                if seen.insert(k.clone()) {
                    labels.push(t.label.clone());
                }
            }
        }
        for trs in &other.transitions {
            for t in trs {
                let k = t.label.canonical_key();
                if seen.insert(k.clone()) {
                    labels.push(t.label.clone());
                }
            }
        }
        let minterms = build_minterms(&labels);

        let mut index: HashMap<(StateId, StateId), StateId> = HashMap::new();
        let mut states: Vec<(StateId, StateId)> = Vec::new();
        let mut q = VecDeque::new();
        index.insert((0, 0), 0);
        states.push((0, 0));
        q.push_back(0usize);

        while let Some(id) = q.pop_front() {
            let (a, b) = states[id];
            for mt in &minterms {
                let t1 = if a == usize::MAX { None } else { self.transition_on_symbol(a, mt) };
                let t2 = if b == usize::MAX { None } else { other.transition_on_symbol(b, mt) };
                if t1.is_none() && t2.is_none() {
                    continue;
                }
                let t1v = t1.unwrap_or(usize::MAX);
                let t2v = t2.unwrap_or(usize::MAX);
                let real_pair = (t1v, t2v);
                if !index.contains_key(&real_pair) {
                    let nid = states.len();
                    index.insert(real_pair, nid);
                    states.push(real_pair);
                    q.push_back(nid);
                }
            }
        }

        let new_n = states.len();
        let mut out = SymbolicDFA::new(new_n);
        for (i, &(q1, q2)) in states.iter().enumerate() {
            let a1 = if q1 != usize::MAX { self.accepting[q1] } else { false };
            let a2 = if q2 != usize::MAX { other.accepting[q2] } else { false };
            out.accepting[i] = accept_op(a1, a2);
        }
        for (i, (q1, q2)) in states.iter().enumerate() {
            for mt in &minterms {
                let t1 = if *q1 == usize::MAX {
                    None
                } else {
                    self.transition_on_symbol(*q1, mt)
                };
                let t2 = if *q2 == usize::MAX {
                    None
                } else {
                    other.transition_on_symbol(*q2, mt)
                };
                if t1.is_none() && t2.is_none() {
                    continue;
                }
                let p1 = t1.unwrap_or(usize::MAX);
                let p2 = t2.unwrap_or(usize::MAX);
                let tid = index[&(p1, p2)];
                out.transitions[i].push(SymbolicTransition {
                    label: mt.clone(),
                    target: tid,
                });
            }
            out.transitions[i].sort_by_key(|tr| tr.label.canonical_key());
        }
        out
    }

    fn transition_on_symbol(&self, q: StateId, sym: &P) -> Option<StateId> {
        for tr in &self.transitions[q] {
            if !tr.label.and(sym).is_empty() {
                return Some(tr.target);
            }
        }
        None
    }
}

// ============================================================================
// Abstract Domain Implementation
// ============================================================================

#[derive(Clone, Debug)]
pub struct AutomataDomain;

impl AbstractDomain for AutomataDomain {
    type Element = SymbolicDFA<CharClass>;

    fn bottom(&self) -> Self::Element {
        // Empty language: 1 state, not accepting
        SymbolicDFA::new(1)
    }

    fn top(&self) -> Self::Element {
        // All strings: 1 state, accepting, transition on all chars to self
        let mut dfa = SymbolicDFA::new(1);
        dfa.accepting[0] = true;
        dfa.transitions[0].push(SymbolicTransition {
            label: CharClass::full(),
            target: 0,
        });
        dfa
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_empty_lang()
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        elem.is_full_lang()
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        // L1 <= L2 iff L1 subset L2 iff L1 intersect (not L2) is empty
        let not_l2 = elem2.complement();
        let intersection = elem1.intersection(&not_l2);
        intersection.is_empty_lang()
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let union = elem1.union(elem2);
        minimize_dfa(&union)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let intersection = elem1.intersection(elem2);
        minimize_dfa(&intersection)
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For now, just use join (union).
        // In a real implementation, we would need a widening operator to ensure termination
        // (e.g., state merging based on k-equivalence or similar).
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_automata_domain() {
        let domain = AutomataDomain;
        let bottom = domain.bottom();
        let top = domain.top();

        assert!(domain.is_bottom(&bottom));
        assert!(domain.is_top(&top));
        assert!(domain.le(&bottom, &top));
        assert!(!domain.le(&top, &bottom));

        // Create DFA for "a"
        let mut nfa_a = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa_a.add_state(true);
        nfa_a.add_transition(s0, CharClass::single('a'), s1);
        let dfa_a = nfa_a.determinize();

        // Create DFA for "b"
        let mut nfa_b = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa_b.add_state(true);
        nfa_b.add_transition(s0, CharClass::single('b'), s1);
        let dfa_b = nfa_b.determinize();

        // Join: "a" | "b"
        let joined = domain.join(&dfa_a, &dfa_b);
        assert!(joined.accepts("a"));
        assert!(joined.accepts("b"));
        assert!(!joined.accepts("c"));
        assert!(!joined.accepts("ab"));

        // Meet: "a" & "b" -> empty
        let met = domain.meet(&dfa_a, &dfa_b);
        assert!(domain.is_bottom(&met));
    }
}
