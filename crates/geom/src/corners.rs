//! Live Corners on any path: the corner anchors where its sides meet at an angle, the sides
//! straight, curved or one of each, and the path with those corners cut round, inverted round or
//! chamfered. Rectangles cut theirs the same way.
//!
//! Between two straight sides a round cut is the circle of the radius tangent to both. A curved
//! side is cut as far from the corner (measured along the curve) as a straight side would be, and
//! a round cut leaves it smoothly there, along its tangent: the cut is close to that circle while
//! the radius is small next to how tightly the side bends. What is left of a curved side is the
//! same curve, shortened.

use kurbo::{CubicBez, ParamCurve, ParamCurveArclen, ParamCurveDeriv, Point, Vec2};

use crate::path::{Anchor, AnchorKind, PathData, SubPath};
use crate::shapes::{CornerKind, KAPPA};

/// Lengths and radii at or below this are none at all.
const EPS: f64 = 1e-9;
/// Straight sides closer than this to straight on (or folded back), as the sine of their angle,
/// make no corner.
const MIN_SINE: f64 = 1e-6;
/// The same where a side is curved, which takes a clearer angle (about 0.57°): art that leaves a
/// line for a curve smoothly often has that anchor marked a corner, its handle a hair off the line.
const MIN_SINE_CURVED: f64 = 1e-2;
/// Lengths along curved sides are measured to this fraction of their control polygon: relative,
/// so that measuring takes a bounded number of steps on a curve of any size.
const ARCLEN_REL: f64 = 1e-7;
/// A curve with a coordinate past this is no side of a corner: measuring it could overflow.
const MAX_CURVE_COORD: f64 = 1e12;

/// A corner Live Corners can cut: an anchor that isn't smooth, between two sides (straight or
/// curved) that leave it at an angle.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Corner {
    /// The anchor's index in its path, counting the anchors of every subpath in order.
    pub index: usize,
    /// Where the sides meet.
    pub at: Point,
    /// Unit directions the sides leave the corner in (a curved side's tangent there): towards
    /// the previous anchor, then towards the next one.
    pub u: Vec2,
    pub v: Vec2,
    /// The sides' lengths (along the curve for a curved one), in the same order.
    pub lu: f64,
    pub lv: f64,
    /// The sides as they run in the path, arriving at the corner then leaving it; `None` where
    /// straight.
    pub sides: [Option<CubicBez>; 2],
}

/// A side of a corner as it runs in the path (`None` where straight) and its length.
type Side = (Option<CubicBez>, f64);

/// The segments of a subpath as sides of its corners, each measured once (two corners share it).
struct Sides(Vec<Option<Option<Side>>>);

impl Sides {
    fn new(sp: &SubPath) -> Self {
        Self(vec![None; sp.anchors.len()])
    }

    /// Segment `j` of `sp` (from anchor `j` to the next) as a side ([`side`]).
    fn get(&mut self, sp: &SubPath, j: usize) -> Option<Side> {
        let slot = self.0.get_mut(j)?;
        *slot.get_or_insert_with(|| side(sp, j))
    }
}

/// Segment `j` of `sp` as a side of a corner: `None` for a curve with a coordinate that isn't
/// finite or is past [`MAX_CURVE_COORD`], or with no length.
fn side(sp: &SubPath, j: usize) -> Option<Side> {
    let (c, straight) = segment(sp, j)?;
    if straight {
        return Some((None, (c.p3 - c.p0).hypot()));
    }
    // (A coordinate that isn't a number fails the comparison, an infinite one the bound.)
    let fits = [c.p0, c.p1, c.p2, c.p3].iter().all(|p| p.x.abs() <= MAX_CURVE_COORD && p.y.abs() <= MAX_CURVE_COORD);
    (fits && polygon(&c) > EPS).then(|| (Some(c), c.arclen(accuracy(&c))))
}

/// Segment `j` of `sp` (from anchor `j` to the next) as a cubic, and whether it is straight.
fn segment(sp: &SubPath, j: usize) -> Option<(CubicBez, bool)> {
    let (a, b) = (sp.anchors.get(j)?, sp.anchors.get((j + 1).checked_rem(sp.anchors.len())?)?);
    Some((CubicBez::new(a.p, a.h_out, b.h_in, b.p), !a.has_out() && !b.has_in()))
}

/// The length of `c`'s control polygon.
fn polygon(c: &CubicBez) -> f64 {
    (c.p1 - c.p0).hypot() + (c.p2 - c.p1).hypot() + (c.p3 - c.p2).hypot()
}

/// How closely lengths along `c` are measured ([`ARCLEN_REL`]).
fn accuracy(c: &CubicBez) -> f64 {
    ARCLEN_REL * polygon(c)
}

/// `c` run backwards.
fn reversed(c: &CubicBez) -> CubicBez {
    CubicBez::new(c.p3, c.p2, c.p1, c.p0)
}

/// `d` at unit length, if it has a length.
fn unit(d: Vec2) -> Option<Vec2> {
    let l = d.hypot();
    (l > EPS && l.is_finite()).then(|| d / l)
}

/// The unit direction `c` leaves its start in: towards its first control point that isn't on
/// the start (a handle of no length leaves the curve's direction to the next one).
fn leaving(c: &CubicBez) -> Option<Vec2> {
    [c.p1, c.p2, c.p3].into_iter().find_map(|p| unit(p - c.p0))
}

impl Corner {
    /// The corner of anchor `i` of `sp`, whose index in the path is `index`, its sides measured
    /// once by `sides`; `None` when the anchor is an end of an open subpath (or the only anchor) or
    /// is smooth, when a side has no length or a curved one can't be measured, or when the sides
    /// leave it straight on.
    fn of(sp: &SubPath, i: usize, index: usize, sides: &mut Sides) -> Option<Self> {
        let n = sp.anchors.len();
        if n < 2 {
            return None;
        }
        let (prev, next) = if sp.closed { ((i + n).checked_sub(1)?.checked_rem(n)?, (i + 1).checked_rem(n)?) } else { (i.checked_sub(1)?, i + 1) };
        let (a, before, after) = (sp.anchors.get(i)?, sp.anchors.get(prev)?, sp.anchors.get(next)?);
        if a.kind == AnchorKind::Smooth {
            return None;
        }
        if !(a.has_in() || a.has_out() || before.has_out() || after.has_in()) {
            // Two straight sides.
            let (du, dv) = (before.p - a.p, after.p - a.p);
            let (lu, lv) = (du.hypot(), dv.hypot());
            if !(lu > EPS && lv > EPS && lu.is_finite() && lv.is_finite()) {
                return None;
            }
            let c = Self { index, at: a.p, u: du / lu, v: dv / lv, lu, lv, sides: [None, None] };
            return (c.sin() > MIN_SINE).then_some(c);
        }
        let ((arriving, lu), (departing, lv)) = (sides.get(sp, prev)?, sides.get(sp, i)?);
        if !(lu > EPS && lv > EPS && lu.is_finite() && lv.is_finite()) {
            return None;
        }
        let u = match &arriving {
            Some(c) => leaving(&reversed(c))?,
            None => (before.p - a.p) / lu,
        };
        let v = match &departing {
            Some(c) => leaving(c)?,
            None => (after.p - a.p) / lv,
        };
        let c = Self { index, at: a.p, u, v, lu, lv, sides: [arriving, departing] };
        (c.sin() > MIN_SINE_CURVED).then_some(c)
    }

    /// The cosine of the angle between the sides.
    pub fn cos(&self) -> f64 {
        self.u.dot(self.v)
    }

    /// The sine of the angle between the sides.
    pub fn sin(&self) -> f64 {
        self.u.cross(self.v).abs()
    }

    /// The angle between the sides, in degrees (90 at a rectangle's corners).
    pub fn angle_deg(&self) -> f64 {
        self.sin().atan2(self.cos()).to_degrees()
    }

    /// How far from the corner a round cut of radius `r` meets each side: r / tan(angle / 2)
    /// (along a curved side, by the angle the sides leave the corner at).
    pub fn setback(&self, r: f64) -> f64 {
        r * (1.0 + self.cos()) / self.sin()
    }

    /// The largest radius the corner draws: its cut then reaches halfway along the shorter side,
    /// so neighbouring corners at their largest meet without overlapping (half the shorter side
    /// at a rectangle's corners).
    pub fn max_radius(&self) -> f64 {
        self.lu.min(self.lv) / 2.0 * self.sin() / (1.0 + self.cos())
    }

    /// The radius the corner is drawn with: `radius`, no larger than [`Corner::max_radius`], 0 when
    /// negative or not a number.
    pub fn fitted(&self, radius: f64) -> f64 {
        radius.max(0.0).min(self.max_radius())
    }

    /// The point `k` along the bisector, measured in (u + v): the centre of a round cut of radius
    /// `r` is at `k = r / sin` (between straight sides).
    pub fn on_bisector(&self, k: f64) -> Point {
        self.at + (self.u + self.v) * k
    }

    /// How much the radius grows when the centre of the round cut moves by `d`: `d`'s part along
    /// the bisector, in radius units.
    pub fn radius_change(&self, d: Vec2) -> f64 {
        d.dot(self.u + self.v) * self.sin() / (2.0 + 2.0 * self.cos())
    }

    /// Where a cut of `radius` (fitted) meets the curved sides: the parameter of the arriving side
    /// (1 at the corner), then of the leaving one (0 at the corner), each [`Corner::setback`]
    /// from the corner along the curve. A straight side keeps its corner end's.
    fn cut_params(&self, radius: f64) -> [f64; 2] {
        let s = self.setback(radius);
        // The parameter `len` along `c` from its start; `none` if that can't be measured.
        let along = |c: &CubicBez, len: f64, none: f64| {
            let t = c.inv_arclen(len, accuracy(c));
            if t.is_nan() { none } else { t.clamp(0.0, 1.0) }
        };
        let [arriving, departing] = &self.sides;
        [arriving.as_ref().map_or(1.0, |c| along(c, (self.lu - s).max(0.0), 1.0)), departing.as_ref().map_or(0.0, |c| along(c, s.min(self.lv), 0.0))]
    }

    /// The ends of a cut of `radius` that meets curved sides at the parameters `t`
    /// ([`Corner::cut_params`]): on the arriving side, then the leaving one, each with the unit
    /// direction its side leaves the corner in there.
    fn ends(&self, radius: f64, [ta, tb]: [f64; 2]) -> [(Point, Vec2); 2] {
        let s = self.setback(radius);
        let [arriving, departing] = self.sides;
        let start = match arriving {
            None => (self.at + self.u * s, self.u),
            Some(c) => {
                let dir = unit(-c.deriv().eval(ta).to_vec2()).or_else(|| leaving(&reversed(&c.subsegment(0.0..ta)))).unwrap_or(self.u);
                (c.eval(ta), dir)
            }
        };
        let end = match departing {
            None => (self.at + self.v * s, self.v),
            Some(c) => {
                let dir = unit(c.deriv().eval(tb).to_vec2()).or_else(|| leaving(&c.subsegment(tb..1.0))).unwrap_or(self.v);
                (c.eval(tb), dir)
            }
        };
        [start, end]
    }

    /// The two anchors replacing the corner when cut with `radius` (> 0, fitted) and `kind`, ending
    /// on curved sides at the parameters `t` ([`Corner::cut_params`]): where the cut meets the
    /// arriving side, then the leaving one. [`cut_corners`] gives them their handles along curved
    /// sides.
    fn cut_with(&self, radius: f64, kind: CornerKind, t: [f64; 2]) -> [Anchor; 2] {
        if self.sides == [None, None] {
            return self.cut_straight(radius, kind);
        }
        let [(start, wu), (end, wv)] = self.ends(radius, t);
        let (h_out, h_in) = match kind {
            // Leaving and reaching the sides along them, as an arc of a circle between those
            // directions would.
            CornerKind::Round => {
                let h = round_handle(start.distance(end), -wu, wv);
                (start - wu * h, end - wv * h)
            }
            CornerKind::InvertedRound => inverted_handles(self.at, start, end).unwrap_or((start, end)),
            CornerKind::Chamfer => (start, end),
        };
        [Anchor { p: start, h_in: start, h_out, kind: AnchorKind::Corner }, Anchor { p: end, h_in, h_out: end, kind: AnchorKind::Corner }]
    }

    /// [`Corner::cut_with`] between two straight sides.
    fn cut_straight(&self, radius: f64, kind: CornerKind) -> [Anchor; 2] {
        let t = self.setback(radius);
        let (start, end) = (self.at + self.u * t, self.at + self.v * t);
        let (h_out, h_in) = match kind {
            // An arc of `radius` tangent to both sides, turning by 180° less the angle.
            CornerKind::Round => {
                let h = radius * arc_handle(-self.cos());
                (start - self.u * h, end - self.v * h)
            }
            // An arc centred on the corner through both ends, spanning the angle.
            CornerKind::InvertedRound => {
                let h = t * arc_handle(self.cos());
                (start + square_to(self.u, self.v) * h, end + square_to(self.v, self.u) * h)
            }
            CornerKind::Chamfer => (start, end),
        };
        [Anchor { p: start, h_in: start, h_out, kind: AnchorKind::Corner }, Anchor { p: end, h_in, h_out: end, kind: AnchorKind::Corner }]
    }

    /// The two anchors of a cut of `radius` (> 0, fitted): [`Corner::cut_with`] where
    /// [`Corner::cut_params`] puts it.
    #[cfg(test)]
    fn cut(&self, radius: f64, kind: CornerKind) -> [Anchor; 2] {
        self.cut_with(radius, kind, self.cut_params(radius))
    }
}

/// The unit direction square to unit `a`, on `b`'s side.
fn square_to(a: Vec2, b: Vec2) -> Vec2 {
    let w = b - a * a.dot(b);
    w / w.hypot()
}

/// The handle length of a cubic leaving one end of a cut along `a` and reaching the other along
/// `b` (unit directions), `chord` apart, as an arc of a circle between them has it: 4/3 ·
/// tan(φ/4) of its radius, φ the turn from `a` to `b`. Between straight sides it is what
/// [`arc_handle`] gives for the radius, and it stays finite at any turn.
fn round_handle(chord: f64, a: Vec2, b: Vec2) -> f64 {
    let cos_half = ((1.0 + a.dot(b).clamp(-1.0, 1.0)) / 2.0).max(0.0).sqrt();
    2.0 * chord / (3.0 * (1.0 + cos_half))
}

/// The handles of an inverted round cut from `start` to `end` about the corner `at`: square to
/// the lines from the corner, as long as those of an arc about it spanning the angle between
/// them. `None` when an end is on the corner or both ends lie one way from it.
fn inverted_handles(at: Point, start: Point, end: Point) -> Option<(Point, Point)> {
    let (eu, ev) = (start - at, end - at);
    let (ru, rv) = (eu.hypot(), ev.hypot());
    let (du, dv) = (unit(eu)?, unit(ev)?);
    let k = arc_handle(du.dot(dv));
    let (su, sv) = (unit(dv - du * du.dot(dv))?, unit(du - dv * dv.dot(du))?);
    Some((start + su * (ru * k), end + sv * (rv * k)))
}

/// The handle length, per unit of radius, of a cubic drawing a circular arc that spans an angle
/// whose cosine is `cos`: 4/3 · tan(angle / 4) ([`KAPPA`] for a quarter circle).
fn arc_handle(cos: f64) -> f64 {
    if cos.abs() < 1e-12 {
        return KAPPA;
    }
    let (sin_half, cos_half) = (((1.0 - cos) / 2.0).max(0.0).sqrt(), ((1.0 + cos) / 2.0).max(0.0).sqrt());
    4.0 / 3.0 * sin_half / (1.0 + cos_half)
}

/// The corners of `path` Live Corners can cut, in anchor order.
pub fn path_corners(path: &PathData) -> Vec<Corner> {
    let mut out = vec![];
    let mut first = 0;
    for sp in &path.subpaths {
        let mut sides = Sides::new(sp);
        out.extend((0..sp.anchors.len()).filter_map(|i| Corner::of(sp, i, first + i, &mut sides)));
        first += sp.anchors.len();
    }
    out
}

/// A corner being cut: its radius (fitted, more than [`EPS`]), its kind and where the cut meets
/// its curved sides ([`Corner::cut_params`]).
struct Cut {
    corner: Corner,
    radius: f64,
    kind: CornerKind,
    t: [f64; 2],
}

/// The radius `radii` (indexed by anchor) cuts corner `c` with, if they cut it at all.
fn cut_radius(c: &Corner, radii: &[f64]) -> Option<f64> {
    let radius = c.fitted(radii.get(c.index).copied().unwrap_or(0.0));
    (radius > EPS).then_some(radius)
}

/// `path` with each of its corners ([`path_corners`]) cut by the radius in `radii` and the kind in
/// `kinds` at its anchor index (missing: 0 and round), each radius no larger than fits
/// ([`Corner::fitted`]). A cut corner becomes two anchors; a closed subpath whose first corner
/// is cut starts where that cut ends, so the cut closes it. A curved side a cut meets keeps its
/// curve, shortened. Also returns, per subpath, the anchor index in `path` each anchor comes from.
pub fn cut_corners(path: &PathData, radii: &[f64], kinds: &[CornerKind]) -> (PathData, Vec<Vec<usize>>) {
    let corners = path_corners(path);
    let mut corners = corners.iter().peekable();
    let (mut subpaths, mut sources) = (Vec::with_capacity(path.subpaths.len()), Vec::with_capacity(path.subpaths.len()));
    let mut first = 0;
    for sp in &path.subpaths {
        let n = sp.anchors.len();
        let mut cuts: Vec<Option<Cut>> = (first..first + n)
            .map(|index| {
                let corner = *corners.next_if(|c| c.index == index)?;
                let radius = cut_radius(&corner, radii)?;
                Some(Cut { corner, radius, kind: kinds.get(index).copied().unwrap_or_default(), t: corner.cut_params(radius) })
            })
            .collect();
        // The anchor segment `j` runs to, where the cuts at either end meet it (0 and 1 where none
        // does, and on a straight segment), and whether either end is cut.
        let span = |cuts: &[Option<Cut>], j: usize| {
            let k = (j + 1).checked_rem(n)?;
            let (from, to) = (cuts.get(j).and_then(Option::as_ref), cuts.get(k).and_then(Option::as_ref));
            Some((k, from.map_or(0.0, |c| c.t[1]), to.map_or(1.0, |c| c.t[0]), from.is_some() || to.is_some()))
        };
        // Two cuts on one curved segment take at most half of it each; measuring to an accuracy
        // may overshoot by a hair, so neither passes the other.
        for j in 0..sp.segment_count() {
            let Some((k, a, b, _)) = span(&cuts, j) else { continue };
            if a > b {
                let m = 0.5 * (a + b);
                if let Some(Some(c)) = cuts.get_mut(j) {
                    c.t[1] = m;
                }
                if let Some(Some(c)) = cuts.get_mut(k) {
                    c.t[0] = m;
                }
            }
        }
        let mut anchors = Vec::with_capacity(n + cuts.iter().flatten().count());
        let mut from = Vec::with_capacity(anchors.capacity());
        // Where each anchor, or its cut, starts and ends in `anchors`.
        let (mut starts, mut ends) = (Vec::with_capacity(n), Vec::with_capacity(n));
        let mut closing = None;
        for (i, a) in sp.anchors.iter().enumerate() {
            let index = first + i;
            match cuts.get(i).and_then(Option::as_ref) {
                Some(c) => {
                    let [start, end] = c.corner.cut_with(c.radius, c.kind, c.t);
                    starts.push(anchors.len());
                    if i == 0 && sp.closed {
                        closing = Some(start);
                    } else {
                        anchors.push(start);
                        from.push(index);
                    }
                    ends.push(anchors.len());
                    anchors.push(end);
                    from.push(index);
                }
                None => {
                    starts.push(anchors.len());
                    ends.push(anchors.len());
                    anchors.push(*a);
                    from.push(index);
                }
            }
        }
        if let Some(a) = closing {
            if let Some(s) = starts.first_mut() {
                *s = anchors.len();
            }
            anchors.push(a);
            from.push(first);
        }
        // What the cuts leave of the curved segments they meet: the same curve, between them (its
        // handles on a cut's new anchor even where the cut is too small to shorten it).
        for j in 0..sp.segment_count() {
            let (Some((k, a, b, true)), Some((c, false))) = (span(&cuts, j), segment(sp, j)) else { continue };
            let rest = c.subsegment(a..b.max(a));
            if let Some(x) = ends.get(j).and_then(|o| anchors.get_mut(*o)) {
                x.h_out = rest.p1;
            }
            if let Some(x) = starts.get(k).and_then(|o| anchors.get_mut(*o)) {
                x.h_in = rest.p2;
            }
        }
        // A round cut leaves a curved side smoothly: that anchor is smooth.
        for (i, c) in cuts.iter().enumerate() {
            if c.as_ref().is_some_and(|c| c.corner.sides != [None, None]) {
                for o in [starts.get(i), ends.get(i)].into_iter().flatten() {
                    if let Some(x) = anchors.get_mut(*o) {
                        x.kind = Anchor::with_handles(x.p, x.h_in, x.h_out).kind;
                    }
                }
            }
        }
        first += n;
        subpaths.push(SubPath::new(anchors, sp.closed));
        sources.push(from);
    }
    (PathData::new(subpaths), sources)
}

/// The anchor of `path` each anchor of `path` cut by `radii` ([`cut_corners`]) comes from, per
/// subpath, without cutting it: `corners` are `path`'s ([`path_corners`]).
pub fn cut_sources(path: &PathData, corners: &[Corner], radii: &[f64]) -> Vec<Vec<usize>> {
    let mut corners = corners.iter().peekable();
    let mut first = 0;
    let mut out = Vec::with_capacity(path.subpaths.len());
    for sp in &path.subpaths {
        let n = sp.anchors.len();
        let mut from = Vec::with_capacity(n);
        let mut closing = false;
        for index in first..first + n {
            let cut = corners.next_if(|c| c.index == index).is_some_and(|c| cut_radius(c, radii).is_some());
            if cut && index == first && sp.closed {
                closing = true;
            } else if cut {
                from.push(index);
            }
            from.push(index);
        }
        if closing {
            from.push(first);
        }
        first += n;
        out.push(from);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shapes;
    use kurbo::{Affine, ParamCurveNearest, Rect};

    fn near(a: Point, b: Point) -> bool {
        a.distance(b) < 1e-9
    }

    fn pt(x: f64, y: f64) -> Point {
        Point::new(x, y)
    }

    /// A corner anchor at `p` with handles at `h_in` and `h_out` (none where `None`).
    fn an(p: (f64, f64), h_in: Option<(f64, f64)>, h_out: Option<(f64, f64)>) -> Anchor {
        let p = pt(p.0, p.1);
        let h = |h: Option<(f64, f64)>| h.map_or(p, |(x, y)| pt(x, y));
        Anchor { p, h_in: h(h_in), h_out: h(h_out), kind: AnchorKind::Corner }
    }

    /// An open path like a frame's side (y down): a straight foot, a corner leaving it for a
    /// curve, a smooth anchor, a long curve (straight in look: its handle runs along it) into a
    /// right angle, and a straight top.
    fn frame() -> PathData {
        let mut smooth = an((6.0, 205.0), Some((6.0, 210.0)), Some((6.0, 150.0)));
        smooth.kind = AnchorKind::Smooth;
        PathData::single(SubPath::new(
            vec![
                an((90.0, 230.0), None, None),
                an((10.0, 230.0), None, None),
                an((10.0, 220.0), None, Some((8.0, 217.0))),
                smooth,
                an((6.0, 8.0), None, None),
                an((90.0, 8.0), None, None),
            ],
            false,
        ))
    }

    /// A D: a straight left side and a curve bulging right, meeting it at right angles.
    fn d_shape() -> PathData {
        PathData::single(SubPath::new(vec![an((0.0, 0.0), Some((80.0, 0.0)), None), an((0.0, 100.0), None, Some((80.0, 100.0)))], true))
    }

    /// A lens: two curves between two corners.
    fn lens() -> PathData {
        PathData::single(SubPath::new(
            vec![an((0.0, 0.0), Some((30.0, 40.0)), Some((30.0, -40.0))), an((100.0, 0.0), Some((70.0, -40.0)), Some((70.0, 40.0)))],
            true,
        ))
    }

    /// A five-pointed star's tips are acute corners, its inner corners obtuse: all ten cut, each
    /// a circle of the radius tangent to both sides.
    #[test]
    fn a_star_has_ten_corners_cut_as_circles() {
        let star = shapes::star(Point::new(100.0, 100.0), 50.0, 25.0, 5, 0.0);
        let corners = path_corners(&star);
        assert_eq!(corners.len(), 10);
        let angles: Vec<_> = corners.iter().map(|c| c.angle_deg()).collect();
        assert!(angles.iter().step_by(2).all(|a| *a < 90.0), "tips are acute: {angles:?}");
        assert!(angles.iter().skip(1).step_by(2).all(|a| *a > 90.0), "inner corners are obtuse: {angles:?}");
        let (cut, from) = cut_corners(&star, &[4.0; 10], &[]);
        assert_eq!(cut.anchor_count(), 20);
        assert_eq!(from, [vec![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 0]]);
        for c in &corners {
            // Both ends of the cut lie `setback` along the sides, as far from the arc's centre as
            // the radius, and that centre is `radius` from either side.
            let t = c.setback(4.0);
            let o = c.on_bisector(4.0 / c.sin());
            for p in [c.at + c.u * t, c.at + c.v * t] {
                assert!((p.distance(o) - 4.0).abs() < 1e-9);
                assert!(cut.anchors().any(|(_, _, a)| near(a.p, p)), "{p:?} is an anchor");
            }
        }
    }

    #[test]
    fn radii_stop_at_half_the_shorter_side_per_corner() {
        let tri = PathData::single(SubPath::polyline(&[Point::new(0.0, 0.0), Point::new(100.0, 0.0), Point::new(0.0, 40.0)], true));
        let corners = path_corners(&tri);
        assert_eq!(corners.len(), 3);
        for c in &corners {
            let max = c.max_radius();
            assert!((c.setback(max) - c.lu.min(c.lv) / 2.0).abs() < 1e-9);
            assert_eq!(c.fitted(1e6), max);
            assert_eq!(c.fitted(-3.0), 0.0);
            assert_eq!(c.fitted(f64::NAN), 0.0);
        }
        // The right angle at (0, 0) takes up to 20, half its shorter side.
        assert!((corners[0].max_radius() - 20.0).abs() < 1e-9);
    }

    #[test]
    fn ends_smooth_and_straight_anchors_are_no_corners() {
        // An open zig-zag: its ends aren't corners, nor is the anchor its sides run straight on through.
        let open = PathData::single(SubPath::polyline(
            &[Point::new(0.0, 0.0), Point::new(50.0, 0.0), Point::new(100.0, 0.0), Point::new(100.0, 50.0), Point::new(150.0, 80.0)],
            false,
        ));
        assert_eq!(path_corners(&open).iter().map(|c| c.index).collect::<Vec<_>>(), [2, 3]);
        // A curve on a side, or a handle on the anchor, still leaves a corner: anchor 1 leaves its
        // side towards (110, 10) at 135°, and anchor 2 takes the curve's direction from that handle
        // (its own end has none).
        let mut sp = SubPath::polyline(&[Point::new(0.0, 0.0), Point::new(100.0, 0.0), Point::new(100.0, 100.0), Point::new(0.0, 100.0)], true);
        sp.anchors[1].h_out = Point::new(110.0, 10.0);
        let p = PathData::single(sp.clone());
        let corners = path_corners(&p);
        assert_eq!(corners.iter().map(|c| c.index).collect::<Vec<_>>(), [0, 1, 2, 3]);
        assert!((corners[1].angle_deg() - 135.0).abs() < 1e-9);
        assert!((corners[2].angle_deg() - (90.0 + (10.0f64 / 90.0).atan().to_degrees())).abs() < 1e-9);
        // Handles in line through the anchor (a smooth join marked a corner) make none, nor do
        // sides that leave it 0.3° off straight on.
        let mut smooth = sp.clone();
        smooth.anchors[1].h_in = Point::new(90.0, -10.0);
        assert_eq!(path_corners(&PathData::single(smooth)).iter().map(|c| c.index).collect::<Vec<_>>(), [0, 2, 3]);
        let a = 0.3f64.to_radians();
        let nearly = PathData::single(SubPath::new(
            vec![
                an((0.0, 0.0), None, None),
                an((100.0, 0.0), None, Some((100.0 + 10.0 * a.cos(), -10.0 * a.sin()))),
                an((200.0, 0.0), None, None),
                an((100.0, 100.0), None, None),
            ],
            true,
        ));
        assert!(!path_corners(&nearly).iter().any(|c| c.index == 1), "a join 0.3° off straight on");
        // Handles 60° apart (a cusp) make a corner.
        let mut cusp = sp;
        cusp.anchors[1].h_in = Point::new(90.0, 0.0);
        cusp.anchors[1].h_out = Point::new(100.0 - 10.0 * 0.5, 10.0 * 3f64.sqrt() / 2.0);
        let corners = path_corners(&PathData::single(cusp));
        let c = corners.iter().find(|c| c.index == 1).unwrap();
        assert!((c.angle_deg() - 60.0).abs() < 1e-9);
        assert!(path_corners(&shapes::ellipse(Rect::new(0.0, 0.0, 10.0, 10.0))).is_empty());
        // A second subpath counts on from the first one's anchors.
        let two = PathData::new(vec![
            SubPath::polyline(&[Point::new(0.0, 0.0), Point::new(10.0, 0.0), Point::new(0.0, 10.0)], true),
            SubPath::polyline(&[Point::new(50.0, 0.0), Point::new(60.0, 0.0), Point::new(50.0, 10.0)], true),
        ]);
        let (cut, from) = cut_corners(&two, &[0.0, 0.0, 0.0, 1.0], &[]);
        assert_eq!(from, [vec![0, 1, 2], vec![3, 4, 5, 3]]);
        assert_eq!(cut.anchor_count(), 7);
    }

    /// Inverted round and chamfer cuts end where the round one does, at any angle.
    #[test]
    fn kinds_share_their_ends() {
        let star = shapes::star(Point::new(0.0, 0.0), 50.0, 25.0, 5, 0.0);
        let ends = |k: CornerKind| -> Vec<Point> { cut_corners(&star, &[3.0; 10], &[k; 10]).0.anchors().map(|(_, _, a)| a.p).collect() };
        let round = ends(CornerKind::Round);
        assert_eq!(ends(CornerKind::InvertedRound), round);
        assert_eq!(ends(CornerKind::Chamfer), round);
        // The inverted arc stays on the circle about the corner.
        let c = path_corners(&star)[0];
        let [s, e] = c.cut(3.0, CornerKind::InvertedRound);
        let bez = kurbo::CubicBez::new(s.p, s.h_out, e.h_in, e.p);
        let r = c.setback(3.0);
        for t in [0.25, 0.5, 0.75] {
            assert!((bez.eval(t).distance(c.at) - r).abs() < r * 1e-3);
        }
    }

    /// The rule before curved sides, word for word: the reference that straight-sided corners
    /// still match exactly.
    mod straight_reference {
        use kurbo::{Point, Vec2};

        use crate::path::{Anchor, AnchorKind, PathData, SubPath};
        use crate::shapes::{CornerKind, KAPPA};

        const EPS: f64 = 1e-9;
        const MIN_SINE: f64 = 1e-6;

        #[derive(Clone, Copy, Debug, PartialEq)]
        pub struct Corner {
            pub index: usize,
            pub at: Point,
            pub u: Vec2,
            pub v: Vec2,
            pub lu: f64,
            pub lv: f64,
        }

        impl Corner {
            fn of(sp: &SubPath, i: usize, index: usize) -> Option<Self> {
                let n = sp.anchors.len();
                let (prev, next) = if sp.closed { ((i + n).checked_sub(1)? % n, (i + 1) % n) } else { (i.checked_sub(1)?, i + 1) };
                let (a, prev, next) = (sp.anchors.get(i)?, sp.anchors.get(prev)?, sp.anchors.get(next)?);
                if a.kind == AnchorKind::Smooth || a.has_in() || a.has_out() || prev.has_out() || next.has_in() {
                    return None;
                }
                let (du, dv) = (prev.p - a.p, next.p - a.p);
                let (lu, lv) = (du.hypot(), dv.hypot());
                if !(lu > EPS && lv > EPS && lu.is_finite() && lv.is_finite()) {
                    return None;
                }
                let c = Self { index, at: a.p, u: du / lu, v: dv / lv, lu, lv };
                (c.sin() > MIN_SINE).then_some(c)
            }
            fn cos(&self) -> f64 {
                self.u.dot(self.v)
            }
            fn sin(&self) -> f64 {
                self.u.cross(self.v).abs()
            }
            fn setback(&self, r: f64) -> f64 {
                r * (1.0 + self.cos()) / self.sin()
            }
            fn max_radius(&self) -> f64 {
                self.lu.min(self.lv) / 2.0 * self.sin() / (1.0 + self.cos())
            }
            fn fitted(&self, radius: f64) -> f64 {
                radius.max(0.0).min(self.max_radius())
            }
            fn cut(&self, radius: f64, kind: CornerKind) -> [Anchor; 2] {
                let t = self.setback(radius);
                let (start, end) = (self.at + self.u * t, self.at + self.v * t);
                let (h_out, h_in) = match kind {
                    CornerKind::Round => {
                        let h = radius * arc_handle(-self.cos());
                        (start - self.u * h, end - self.v * h)
                    }
                    CornerKind::InvertedRound => {
                        let h = t * arc_handle(self.cos());
                        (start + square_to(self.u, self.v) * h, end + square_to(self.v, self.u) * h)
                    }
                    CornerKind::Chamfer => (start, end),
                };
                [Anchor { p: start, h_in: start, h_out, kind: AnchorKind::Corner }, Anchor { p: end, h_in, h_out: end, kind: AnchorKind::Corner }]
            }
        }

        fn square_to(a: Vec2, b: Vec2) -> Vec2 {
            let w = b - a * a.dot(b);
            w / w.hypot()
        }

        fn arc_handle(cos: f64) -> f64 {
            if cos.abs() < 1e-12 {
                return KAPPA;
            }
            let (sin_half, cos_half) = (((1.0 - cos) / 2.0).max(0.0).sqrt(), ((1.0 + cos) / 2.0).max(0.0).sqrt());
            4.0 / 3.0 * sin_half / (1.0 + cos_half)
        }

        pub fn path_corners(path: &PathData) -> Vec<Corner> {
            let mut out = vec![];
            let mut first = 0;
            for sp in &path.subpaths {
                out.extend((0..sp.anchors.len()).filter_map(|i| Corner::of(sp, i, first + i)));
                first += sp.anchors.len();
            }
            out
        }

        pub fn cut_corners(path: &PathData, radii: &[f64], kinds: &[CornerKind]) -> (PathData, Vec<Vec<usize>>) {
            let corners = path_corners(path);
            let mut corners = corners.iter().peekable();
            let (mut subpaths, mut sources) = (Vec::with_capacity(path.subpaths.len()), Vec::with_capacity(path.subpaths.len()));
            let mut first = 0;
            for sp in &path.subpaths {
                let (mut anchors, mut from) = (Vec::with_capacity(sp.anchors.len()), Vec::with_capacity(sp.anchors.len()));
                let mut closing = None;
                for (i, a) in sp.anchors.iter().enumerate() {
                    let index = first + i;
                    let corner = corners.next_if(|c| c.index == index);
                    let radius = corner.map_or(0.0, |c| c.fitted(radii.get(index).copied().unwrap_or(0.0)));
                    match corner {
                        Some(c) if radius > EPS => {
                            let [start, end] = c.cut(radius, kinds.get(index).copied().unwrap_or_default());
                            if i == 0 && sp.closed {
                                closing = Some(start);
                            } else {
                                anchors.push(start);
                                from.push(index);
                            }
                            anchors.push(end);
                            from.push(index);
                        }
                        _ => {
                            anchors.push(*a);
                            from.push(index);
                        }
                    }
                }
                if let Some(a) = closing {
                    anchors.push(a);
                    from.push(first);
                }
                first += sp.anchors.len();
                subpaths.push(SubPath::new(anchors, sp.closed));
                sources.push(from);
            }
            (PathData::new(subpaths), sources)
        }
    }

    /// Straight-sided corners find and cut exactly as before curved sides counted: rectangles,
    /// stars, polygons, a triangle, an open zig-zag and two subpaths, every kind, any radius.
    #[test]
    fn straight_cuts_match_the_straight_rule_bit_for_bit() {
        let mut paths = vec![
            shapes::rectangle(Rect::new(10.0, 20.0, 110.0, 80.0)),
            PathData::single(SubPath::polyline(&[pt(0.0, 0.0), pt(100.0, 0.0), pt(0.0, 40.0)], true)),
            PathData::single(SubPath::polyline(&[pt(0.0, 0.0), pt(50.0, 0.0), pt(100.0, 0.0), pt(100.0, 50.0), pt(150.0, 80.0)], false)),
            PathData::new(vec![
                SubPath::polyline(&[pt(0.0, 0.0), pt(10.0, 0.0), pt(0.0, 10.0)], true),
                SubPath::polyline(&[pt(50.0, 0.0), pt(60.0, 0.0), pt(50.0, 10.0)], true),
            ]),
        ];
        for points in [5, 7] {
            paths.push(shapes::star(pt(50.0, 60.0), 40.0, 15.0, points, 17.0));
        }
        for sides in 3..=8 {
            paths.push(shapes::polygon(pt(-30.0, 45.0), 33.0, sides, 11.0));
        }
        for path in &paths {
            let (new, old) = (path_corners(path), straight_reference::path_corners(path));
            assert_eq!(new.len(), old.len());
            for (a, b) in new.iter().zip(&old) {
                assert_eq!((a.index, a.at, a.u, a.v, a.lu, a.lv, a.sides), (b.index, b.at, b.u, b.v, b.lu, b.lv, [None, None]));
            }
            let n = path.anchor_count();
            for r in [0.0, 3.0, 1e6, -5.0, f64::NAN] {
                let kinds: [Vec<CornerKind>; 4] =
                    [vec![], vec![CornerKind::InvertedRound; n], vec![CornerKind::Chamfer; n], (0..n).map(|i| CornerKind::ALL[i % 3]).collect()];
                for kinds in kinds {
                    let radii: Vec<f64> = (0..n).map(|i| if i % 4 == 3 { 0.0 } else { r }).collect();
                    assert_eq!(cut_corners(path, &radii, &kinds), straight_reference::cut_corners(path, &radii, &kinds), "{path:?} at {r}");
                }
            }
        }
        // A path with curved corners too cuts its straight one as the rule does, and leaves what
        // its curved cuts don't reach alone.
        let frame = frame();
        let only_straight = [0.0, 4.0, 0.0, 0.0, 0.0, 0.0];
        assert_eq!(cut_corners(&frame, &only_straight, &[]), straight_reference::cut_corners(&frame, &only_straight, &[]));
        let all = cut_corners(&frame, &[4.0; 6], &[]).0;
        let reference = straight_reference::cut_corners(&frame, &[4.0; 6], &[]).0;
        assert_eq!(all.subpaths[0].anchors[..3], reference.subpaths[0].anchors[..3]);
    }

    /// A corner between a line and a curve, or two curves, counts: the frame's foot (straight),
    /// the corner leaving it for a curve and the right angle the long curve arrives at, not its
    /// ends nor its smooth anchor.
    #[test]
    fn corners_between_curves_and_lines_qualify() {
        let frame = frame();
        let corners = path_corners(&frame);
        assert_eq!(corners.iter().map(|c| c.index).collect::<Vec<_>>(), [1, 2, 4]);
        let [foot, leave, right] = [corners[0], corners[1], corners[2]];
        assert!(foot.sides == [None, None] && (foot.angle_deg() - 90.0).abs() < 1e-9);
        // Leaving the foot towards (8, 217): the curve's direction there.
        assert!(leave.sides[0].is_none() && leave.sides[1].is_some());
        assert!((leave.angle_deg() - (180.0 - (2.0f64 / 3.0).atan().to_degrees())).abs() < 1e-9);
        // The long curve's own end has no handle: it arrives along its other handle, straight down.
        assert!(right.sides[0].is_some() && right.sides[1].is_none());
        assert!((right.angle_deg() - 90.0).abs() < 1e-9);
        // Its length is along the curve.
        let curve = frame.subpaths[0].segment(3);
        assert!((right.lu - curve.arclen(1e-12)).abs() < 1e-4, "{} vs {}", right.lu, curve.arclen(1e-12));
        assert!((right.lu - 197.0).abs() < 1e-4);
        assert_eq!(right.lv, 84.0);
        // The lens's two corners are between curves.
        let corners = path_corners(&lens());
        assert_eq!(corners.len(), 2);
        assert!(corners.iter().all(|c| c.sides.iter().all(Option::is_some)));
        assert!((corners[0].angle_deg() - (180.0 - 2.0 * (3.0f64 / 4.0).atan().to_degrees())).abs() < 1e-9);
    }

    /// Where a round cut meets a curved side, it starts `setback` along the curve from the corner
    /// and leaves it smoothly; what is left of each side lies on its curve; the anchors away from
    /// the cuts stay as they were.
    #[test]
    fn curved_cuts_meet_their_sides_smoothly() {
        for (name, path) in [("D", d_shape()), ("lens", lens()), ("frame", frame())] {
            let corners = path_corners(&path);
            let n = path.anchor_count();
            let (cut, from) = cut_corners(&path, &vec![4.0; n], &[]);
            let (sp, out, from) = (&path.subpaths[0], &cut.subpaths[0], &from[0]);
            assert_eq!(out.anchors.len(), n + corners.len(), "{name}");
            for c in &corners {
                let t = c.cut_params(4.0);
                let s = c.setback(4.0);
                if let Some(side) = c.sides[0] {
                    assert!((side.subsegment(t[0]..1.0).arclen(1e-12) - s).abs() < 1e-6 * c.lu, "{name}: corner {} arriving", c.index);
                }
                if let Some(side) = c.sides[1] {
                    assert!((side.subsegment(0.0..t[1]).arclen(1e-12) - s).abs() < 1e-6 * c.lv, "{name}: corner {} leaving", c.index);
                }
                let [(start, _), (end, _)] = c.ends(4.0, t);
                for p in [start, end] {
                    assert!(out.anchors.iter().any(|a| a.p == p), "{name}: {p:?} is an anchor");
                }
            }
            // Where a cut meets a curve, its anchor's handles are in line on either side.
            let mut smooth = 0;
            for (o, a) in out.anchors.iter().enumerate() {
                if a.has_in() && a.has_out() && corners.iter().any(|c| c.index == from[o]) {
                    let (i, x) = (a.h_in - a.p, a.h_out - a.p);
                    assert!(i.cross(x).abs() <= 1e-9 * i.hypot() * x.hypot() && i.dot(x) < 0.0, "{name}: anchor {o} {a:?}");
                    assert_eq!(a.kind, AnchorKind::Smooth, "{name}: anchor {o}");
                    smooth += 1;
                }
            }
            let curved_ends: usize = corners.iter().map(|c| c.sides.iter().flatten().count()).sum();
            assert_eq!(smooth, curved_ends, "{name}");
            // Every segment but the cuts is what is left of the one it comes from, on its curve; so
            // too with cuts too small to shorten their sides by much.
            for r in [4.0, 1e-7] {
                let (cut, from) = cut_corners(&path, &vec![r; n], &[]);
                let (out, from) = (&cut.subpaths[0], &from[0]);
                let m = out.anchors.len();
                for o in 0..out.segment_count() {
                    let (fa, fb) = (from[o], from[(o + 1) % m]);
                    if fa == fb {
                        continue;
                    }
                    let (original, rest) = (sp.segment(fa), out.segment(o));
                    for t in [0.0, 0.25, 0.5, 0.75, 1.0] {
                        let q = rest.eval(t);
                        let d = original.nearest(q, 1e-12).distance_sq.sqrt();
                        assert!(d < 1e-7, "{name} at {r}: segment {o} at {t} is {d} off");
                    }
                }
            }
        }
        // The frame's ends stay; its smooth anchor stays smooth, its handles shortened along
        // their own directions.
        let frame = frame();
        let (before, after) = (&frame.subpaths[0].anchors, cut_corners(&frame, &[4.0; 6], &[]).0.subpaths[0].anchors.clone());
        assert_eq!((after.first(), after.last()), (before.first(), before.last()));
        let smooth = after.iter().find(|a| a.p == pt(6.0, 205.0)).unwrap();
        assert_eq!(smooth.kind, AnchorKind::Smooth);
        let dir = |v: Vec2| v / v.hypot();
        assert!(near(dir(smooth.h_in - smooth.p).to_point(), pt(0.0, 1.0)) && near(dir(smooth.h_out - smooth.p).to_point(), pt(0.0, -1.0)));
        assert!((smooth.h_in - smooth.p).hypot() < 5.0 && (smooth.h_out - smooth.p).hypot() < 55.0);
    }

    /// A curved side's corners at their largest take half of it each, by length, and meet there.
    #[test]
    fn curved_radii_stop_at_half_the_shorter_arc() {
        let lens = lens();
        let corners = path_corners(&lens);
        for c in &corners {
            assert!((c.setback(c.max_radius()) - c.lu.min(c.lv) / 2.0).abs() < 1e-9 * c.lu);
            assert_eq!(c.fitted(1e6), c.max_radius());
        }
        let (cut, from) = cut_corners(&lens, &[1e6; 2], &[]);
        assert_eq!(from, [vec![0, 1, 1, 0]]);
        let a = &cut.subpaths[0].anchors;
        // [the end of corner 0's cut, corner 1's cut, the start of corner 0's]: the ends on each
        // side meet halfway along it.
        assert!(a[0].p.distance(a[1].p) < 1e-5, "{a:?}");
        assert!(a[2].p.distance(a[3].p) < 1e-5, "{a:?}");
        let top = lens.subpaths[0].segment(0);
        let t = top.nearest(a[0].p, 1e-12).t;
        assert!((top.subsegment(0.0..t).arclen(1e-12) - top.arclen(1e-12) / 2.0).abs() < 1e-5);
        assert!(cut.anchors().all(|(_, _, x)| [x.p, x.h_in, x.h_out].iter().all(|p| p.is_finite())));
        // The D's curve is longer than its straight side: the straight side stops both corners.
        let d = d_shape();
        for c in path_corners(&d) {
            assert!(c.lu.min(c.lv) == 100.0 && c.lu.max(c.lv) > 100.0);
        }
    }

    /// On curved sides too, inverted round and chamfer cuts end where the round one does; the
    /// inverted one leaves its ends square to the lines from the corner, the chamfer straight.
    #[test]
    fn kinds_share_their_ends_on_curves() {
        for path in [d_shape(), lens(), frame()] {
            let n = path.anchor_count();
            let ends = |k: CornerKind| -> Vec<Point> { cut_corners(&path, &vec![4.0; n], &vec![k; n]).0.anchors().map(|(_, _, a)| a.p).collect() };
            let round = ends(CornerKind::Round);
            assert_eq!(ends(CornerKind::InvertedRound), round);
            assert_eq!(ends(CornerKind::Chamfer), round);
            for c in path_corners(&path).iter().filter(|c| c.sides != [None, None]) {
                let [s, e] = c.cut(4.0, CornerKind::InvertedRound);
                assert!((s.h_out - s.p).dot((s.p - c.at) / (s.p - c.at).hypot()).abs() < 1e-9);
                assert!((e.h_in - e.p).dot((e.p - c.at) / (e.p - c.at).hypot()).abs() < 1e-9);
                assert!(s.has_out() && e.has_in());
                let [s, e] = c.cut(4.0, CornerKind::Chamfer);
                assert_eq!((s.h_out, e.h_in), (s.p, e.p));
            }
        }
    }

    #[test]
    fn cut_sources_matches_cut_corners() {
        let star = shapes::star(pt(100.0, 100.0), 50.0, 25.0, 5, 0.0);
        let two = PathData::new(vec![d_shape().subpaths[0].clone(), lens().subpaths[0].clone(), frame().subpaths[0].clone()]);
        let cases: Vec<(PathData, Vec<f64>)> = vec![
            (star.clone(), vec![4.0; 10]),
            (star, (0..10).map(|i| if i % 3 == 0 { 2.0 } else { 0.0 }).collect()),
            (d_shape(), vec![4.0, 0.0]),
            (d_shape(), vec![0.0, 4.0]),
            (lens(), vec![3.0, 3.0]),
            (frame(), vec![0.0, 4.0, 4.0, 4.0, 4.0, 0.0]),
            (frame(), vec![]),
            (two, (0..10).map(|i| (i % 2) as f64 * 5.0).collect()),
        ];
        for (path, radii) in cases {
            assert_eq!(cut_sources(&path, &path_corners(&path), &radii), cut_corners(&path, &radii, &[]).1, "{radii:?}");
        }
    }

    /// Sides of no length, handles of almost none, cusps, loops, tiny and huge shapes, and
    /// handles that aren't numbers: every cut comes out finite (for a finite path), with one anchor
    /// more per cut corner, at any radius.
    #[test]
    fn degenerate_curved_sides_cut_without_nan() {
        let square =
            |a1: Anchor, a2: Anchor| PathData::single(SubPath::new(vec![an((0.0, 0.0), None, None), a1, a2, an((0.0, 100.0), None, None)], true));
        let plain2 = an((100.0, 100.0), None, None);
        let mut paths = vec![
            // Handles of 1e-10 (none) and 1e-8 (one).
            square(an((100.0, 0.0), None, Some((100.0, 1e-10))), plain2),
            square(an((100.0, 0.0), None, Some((100.0, 1e-8))), plain2),
            // The curve's first three points on the anchor.
            square(an((100.0, 0.0), None, None), an((100.0, 100.0), Some((100.0, 0.0)), None)),
            // Its last two points on the next anchor.
            square(an((100.0, 0.0), None, Some((100.0, 100.0))), plain2),
            // A cusp mid-side: handles folded back past each other.
            square(an((100.0, 0.0), None, Some((100.0, 150.0))), an((100.0, 100.0), Some((100.0, -50.0)), None)),
            // A loop: handles crossed.
            square(an((100.0, 0.0), None, Some((150.0, 150.0))), an((100.0, 100.0), Some((150.0, -50.0)), None)),
            // A side from an anchor back to the same place.
            PathData::single(SubPath::new(
                vec![an((0.0, 0.0), Some((-40.0, 60.0)), Some((40.0, 60.0))), an((0.0, 0.0), Some((60.0, -40.0)), Some((-60.0, -40.0)))],
                true,
            )),
            // A teardrop: one anchor, closed.
            PathData::single(SubPath::new(vec![an((0.0, 0.0), Some((-50.0, 100.0)), Some((50.0, 100.0)))], true)),
            d_shape().transformed(Affine::scale(1e-8)),
            lens().transformed(Affine::translate((1e11, 1e11))),
            lens().transformed(Affine::translate((1e13, 0.0))),
            lens().transformed(Affine::scale(1e298)),
            square(an((100.0, 0.0), None, Some((f64::NAN, 5.0))), plain2),
            square(an((100.0, 0.0), None, Some((f64::INFINITY, 5.0))), plain2),
        ];
        paths.push(frame().transformed(Affine::rotate(0.3)));
        let finite = |a: &Anchor| [a.p, a.h_in, a.h_out].iter().all(|p| p.is_finite());
        for path in &paths {
            let n = path.anchor_count();
            let corners = path_corners(path);
            for r in [0.0, 1e-300, 1.0, 1e6, 1e308, f64::INFINITY, f64::NAN, -1.0] {
                for kind in CornerKind::ALL {
                    let radii = vec![r; n];
                    let (cut, from) = cut_corners(path, &radii, &vec![kind; n]);
                    if path.anchors().all(|(_, _, a)| finite(a)) {
                        assert!(cut.anchors().all(|(_, _, a)| finite(a)), "{path:?} at {r} {kind:?}: {cut:?}");
                    }
                    let cuts = corners.iter().filter(|c| cut_radius(c, &radii).is_some()).count();
                    assert_eq!(cut.anchor_count(), n + cuts, "{path:?} at {r}");
                    assert_eq!(cut.subpaths.iter().map(|s| s.anchors.len()).collect::<Vec<_>>(), from.iter().map(Vec::len).collect::<Vec<_>>());
                    assert_eq!(from, cut_sources(path, &corners, &radii));
                }
            }
        }
        // Huge or broken curves are no sides; the teardrop's lone anchor no corner.
        assert!(path_corners(&lens().transformed(Affine::translate((1e13, 0.0)))).is_empty());
        assert!(path_corners(&paths[7]).is_empty());
        assert_eq!(path_corners(&lens().transformed(Affine::translate((1e11, 1e11)))).len(), 2);
    }
}
