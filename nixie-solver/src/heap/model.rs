//! Concrete map semantics, independent of the pairwise SMT encoding.

use super::*;
use nixie_core::ast::TermKind;
use num_traits::Zero;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Integer(BigInt),
    Boolean(bool),
}

fn integer(values: &[Value], i: usize) -> Result<&BigInt, HeapError> {
    match values.get(i) {
        Some(Value::Integer(n)) => Ok(n),
        _ => Err(HeapError("invalid integer in heap model evaluation")),
    }
}

fn boolean(values: &[Value], i: usize) -> Result<bool, HeapError> {
    match values.get(i) {
        Some(Value::Boolean(b)) => Ok(*b),
        _ => Err(HeapError("invalid Boolean in heap model evaluation")),
    }
}

// Duplicate locations invalidate a separating conjunction even if values agree.
// This map construction neither inspects nor evaluates any reduction constraint.
fn concrete(
    spatial: &Spatial,
    values: &[Value],
) -> Result<Option<BTreeMap<BigInt, BigInt>>, HeapError> {
    let mut cells = BTreeMap::new();
    for &(l, v) in &spatial.cells {
        let location = integer(values, l)?;
        if location.is_zero()
            || cells
                .insert(location.clone(), integer(values, v)?.clone())
                .is_some()
        {
            return Ok(None);
        }
    }
    Ok(Some(cells))
}

impl HeapSolver {
    fn values(&self, model: &HeapModel) -> Result<Vec<Value>, HeapError> {
        if !Arc::ptr_eq(&self.owner, &model.owner) {
            return Err(HeapError("model belongs to another heap solver"));
        }
        if model.cells.contains_key(&BigInt::zero()) {
            return Err(HeapError("nil is allocated in heap model"));
        }
        let mut values = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let value = match node {
                Node::Integer(n) => Value::Integer(n.clone()),
                Node::Boolean(b) => Value::Boolean(*b),
                Node::IntVar(name) => Value::Integer(
                    model
                        .integers
                        .get(name)
                        .ok_or(HeapError("missing integer assignment"))?
                        .clone(),
                ),
                Node::BoolVar(name) => Value::Boolean(
                    *model
                        .booleans
                        .get(name)
                        .ok_or(HeapError("missing Boolean assignment"))?,
                ),
                Node::Add(a, b) => Value::Integer(integer(&values, *a)? + integer(&values, *b)?),
                Node::Sub(a, b) => Value::Integer(integer(&values, *a)? - integer(&values, *b)?),
                Node::Scale(c, a) => Value::Integer(c * integer(&values, *a)?),
                Node::Eq(a, b) => Value::Boolean(integer(&values, *a)? == integer(&values, *b)?),
                Node::Le(a, b) => Value::Boolean(integer(&values, *a)? <= integer(&values, *b)?),
                Node::Not(a) => Value::Boolean(!boolean(&values, *a)?),
                Node::And(args) => {
                    let mut all = true;
                    for &a in args {
                        all &= boolean(&values, a)?;
                    }
                    Value::Boolean(all)
                }
                Node::Or(args) => {
                    let mut any = false;
                    for &a in args {
                        any |= boolean(&values, a)?;
                    }
                    Value::Boolean(any)
                }
                Node::Heap(i) => {
                    let spatial = self
                        .spatial
                        .get(*i)
                        .ok_or(HeapError("missing heaplet definition"))?;
                    Value::Boolean(concrete(spatial, &values)?.as_ref() == Some(&model.cells))
                }
            };
            values.push(value);
        }
        Ok(values)
    }

    /// Independently evaluate an original formula on a concrete model. This
    /// walks the original arena, not generated SMT constraints or assignments
    /// to compound terms. Exact integer arithmetic is used throughout.
    pub fn evaluate(&self, formula: &Formula, model: &HeapModel) -> Result<bool, HeapError> {
        let index = self.index(&formula.0)?;
        boolean(&self.values(model)?, index)
    }

    /// Validate the original active assertions and the concrete heap. The
    /// checker does not trust the backend's assignments to heap atoms.
    pub fn validate_model(&self, model: &HeapModel) -> Result<(), HeapError> {
        let values = self.values(model)?;
        for &assertion in &self.assertions {
            if !boolean(&values, assertion)? {
                return Err(HeapError(
                    "concrete heap model violates an original assertion",
                ));
            }
        }
        Ok(())
    }

    pub(super) fn selected_heap(&self) -> Result<Option<usize>, HeapError> {
        let backend = self
            .backend
            .model()
            .ok_or(HeapError("missing backend model"))?;
        let mut selected = None;
        for (index, spatial) in self.spatial.iter().enumerate() {
            match backend.get(spatial.atom) {
                None => {} // Candidate false completion, independently checked below.
                Some(value) => match self.tm.get(value).map(|t| &t.kind) {
                    Some(TermKind::True) => {
                        if selected.is_none() {
                            selected = Some(index);
                        }
                    }
                    Some(TermKind::False) => {}
                    _ => return Err(HeapError("non-concrete heap atom in backend model")),
                },
            }
        }
        Ok(selected)
    }

    pub(super) fn extract_model(&self) -> Result<HeapModel, HeapError> {
        let backend = self
            .backend
            .model()
            .ok_or(HeapError("missing backend model"))?;
        let mut model = HeapModel {
            owner: self.owner.clone(),
            cells: BTreeMap::new(),
            integers: BTreeMap::new(),
            booleans: BTreeMap::new(),
        };
        for (node, &term) in self.nodes.iter().zip(&self.terms) {
            match node {
                Node::IntVar(name) => {
                    // Explicit model completion: choose zero for an omitted
                    // variable, then validate ALL original assertions. This
                    // is a candidate assignment, never evidence by itself.
                    let value = match backend.get(term) {
                        None => BigInt::zero(),
                        Some(value) => match self.tm.get(value).map(|t| &t.kind) {
                            Some(TermKind::IntConst(n)) => n.clone(),
                            Some(TermKind::RealConst(n)) if *n.denom() == 1 => {
                                BigInt::from(*n.numer())
                            }
                            _ => return Err(HeapError("non-concrete integer in backend model")),
                        },
                    };
                    model.integers.insert(name.clone(), value);
                }
                Node::BoolVar(name) => {
                    let value = match backend.get(term) {
                        None => false,
                        Some(value) => match self.tm.get(value).map(|t| &t.kind) {
                            Some(TermKind::True) => true,
                            Some(TermKind::False) => false,
                            _ => return Err(HeapError("non-concrete Boolean in backend model")),
                        },
                    };
                    model.booleans.insert(name.clone(), value);
                }
                Node::Integer(_)
                | Node::Boolean(_)
                | Node::Add(..)
                | Node::Sub(..)
                | Node::Scale(..)
                | Node::Eq(..)
                | Node::Le(..)
                | Node::Not(_)
                | Node::And(_)
                | Node::Or(_)
                | Node::Heap(_) => {}
            }
        }
        let values = self.values(&model)?;
        if let Some(index) = self.selected_heap()? {
            model.cells = concrete(&self.spatial[index], &values)?
                .ok_or(HeapError("backend selected an invalid heaplet"))?;
            return Ok(model);
        }
        // Every exact heaplet false: cardinality alone distinguishes this
        // witness from ALL registered heaplets, independently of aliases or
        // data. There is no bounded-heap assumption: integers are infinite.
        let max = self
            .spatial
            .iter()
            .map(|s| s.cells.len())
            .max()
            .unwrap_or(0);
        for i in 0..=max {
            model.cells.insert(BigInt::from(i) + 1, BigInt::zero());
        }
        Ok(model)
    }
}
