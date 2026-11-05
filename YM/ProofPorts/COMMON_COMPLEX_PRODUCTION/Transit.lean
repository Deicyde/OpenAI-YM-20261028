import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Bath
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Exchange

/-!
# Differentiating at the represented healthy boundary, before indicators

Unforced germ even at the corners. Qualitative hypothesis on a fixed
component chart here (`Around`, not uniform extension radius): integrable
domination w.r.t. REAL partially pinned coordinates on a neighborhood.
Derive the actual ordered left jet, with reference law back at original U.
No analytic dependence of the full density / discarded defaults required.
Fixed-argument hard tests, not interchanges of contour integrals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss Puff
open scoped Topology BigOperators Classical MatrixOrder ContDiff
variable {G : Gauge} {n : Side} {T : Bath G n}

structure Cabin (T : Bath G n) where
  pin : Pin G T.axis
  shift : T.tag → Config G n → pin.Shift
  copy : T.tag → Config G n → pin.Group

namespace Cabin
variable (C : Cabin T)

abbrev State := T.tag × C.pin.State

def charge := T.bill.prod C.pin.basis
instance : SFinite C.charge := by unfold charge; infer_instance

def cross (F : Config G n → T.tag → T.Play → ℂ) (p : C.State) (W : Config G n) : ℂ :=
    C.pin.pinned (T.cov W p.1) (C.shift p.1 W) (C.copy p.1 W) (F W p.1) p.2

def post (F : Config G n → T.tag → T.Play → ℂ) (c : ℂ) (U : Config G n) (l : List (Directions G n)) (x : T.tag) : T.Play→ℂ :=
  C.pin.returnWeight (T.cov U x) (C.shift x U) (C.copy x U) (fun a => c * leftDerivs (C.cross F (x,a)) l U)

def rate (p : C.State) (W : Config G n) : ℝ := C.pin.kernel (T.cov W p.1) (C.shift p.1 W) (C.copy p.1 W) p.2

def retrace (p : C.State) (W : Config G n) := C.pin.rewind (C.shift p.1 W) (C.copy p.1 W) p.2

def pickUp (x : T.tag) (U : Config G n) (z : T.Play) : C.State := (x,C.pin.fetch (C.shift x U) (C.copy x U) z)

/-- Physical output chart conditions, not quantitative component-cost
producers. C and μ on whole healthy *extension*, even with jointly priced
hard/soft variants. Whenever a positive-order price or just interchanging
at the boundary, need crude dominance on the *open* neighbor fields
with all protects fixed. All conditional score bounds to be read on
`post`, using the SAME cov as here and in the first-system assembly.
Use local witnesses independent of pinned values for the open sets. -/
structure Around (F : Config G n → T.tag → T.Play → ℂ) (U : Config G n) (k : ℕ) where
  clean : C.pin.Clean
  hood : Set (Config G n)
  openH : IsOpen hood
  inside : U∈hood
  pos V : V∈hood → ∀ x, (T.cov V x).PosDef
  protect V : V∈hood → ∀ θ z, z ∉ C.pin.trace (C.shift θ V) → F V θ z = 0
  packed (l : List (Directions G n)) : l.length ≤ k → Measurable (fun y => leftDerivs (C.cross F y) l U)
  collar (x : C.State) (l : List (Directions G n)) : l.length ≤ k → leftDerivs (C.cross F x) l U ≠ 0 →
      ∀ᶠ W in 𝓝 U,x.2∈C.pin.scan (C.copy x.1 W)
  here V : V∈hood → ∀ x, Measurable (fun y => C.cross F (x,y) V)
  thermal i V : V∈hood → Crest k (C.cross F i) V
  coords : ∃ O : Set (Directions G n), 0∈O ∧ Crud C.charge O (fun j v => C.cross F j (increment U v)) k
  cuffs (l : List (Directions G n)) : l.length ≤ k → ∃ g : C.State→ℝ, Integrable g C.charge ∧
      (∀ W∈hood,AEStronglyMeasurable (fun j => leftDerivs (C.cross F j) l W) C.charge) ∧
      ∀ᵐ j ∂C.charge, ∀ W∈hood, ‖leftDerivs (C.cross F j) l W‖ ≤ g j

namespace Around
variable {C} {F : Config G n → T.tag → T.Play → ℂ} {U : Config G n} {k : ℕ} (h : C.Around F U k)

include h
private lemma comp_eq (V : Config G n) (hv : V∈h.hood) (x:T.tag) : T.sectionAt V (F V) x = ∫ y,C.cross F (x,y) V ∂C.pin.basis :=
  (h.clean.pinned_price (C.shift x V) (C.copy x V) _ (h.pos V hv x) (F V x) (h.here V hv x) (h.protect V hv x)).2.symm

private lemma agree (V : Config G n) (hv : V∈h.hood) : T.readout V (F V) = ∫ y,C.cross F y V ∂C.charge := by
  obtain ⟨g,hg,hm,hG⟩:=h.cuffs [] (Nat.zero_le _)
  have hi : Integrable (fun j => C.cross F j V) C.charge := hg.mono' (hm V hv) (hG.mono fun j hj => hj V hv)
  rw [Cabin.charge, integral_prod (fun j => C.cross F j V) hi]; unfold Bath.readout
  apply integral_congr_ae
  exact Eventually.of_forall (h.comp_eq V hv)

def furnished : Implanted C.charge U k (C.cross F) (fun V => T.readout V (F V)) where
  hood:=h.hood
  openH:=h.openH
  inside:=h.inside
  agreement V := h.agree V
  thermal i V hv := (h.thermal i V hv).germ
  coords := h.coords
  cuffs := h.cuffs

lemma reheated {c : ℂ} {l : List (Directions G n)} {p : C.State} (hl : l.length ≤ k)
    (hp : c*leftDerivs (C.cross F p) l U≠0) :
    (c • C.cross F p) =ᶠ[𝓝 U] fun V => (C.rate p V:ℂ) * (c * F V p.1 (C.retrace p V)) := by
  filter_upwards [h.collar p l hl (right_ne_zero_of_mul hp)] with V hv
  rw [Pi.smul_apply,cross,Pin.pinned,Set.indicator_of_mem hv,Complex.real_smul,smul_eq_mul,mul_left_comm]; rfl

lemma charged (l : List (Directions G n)) (hl : l.length ≤ k) (c : ℂ) :
    leftDerivs (c • fun W => T.readout W (F W)) l U = ∫ x, ∫ z,C.post F c U l x z ∂standard _ ∂T.bill := by
  rw [scaled_left,h.furnished.done l hl U h.furnished.inside, ← integral_const_mul]
  obtain ⟨g,hg,hm,hG⟩ := h.cuffs l hl
  rw [Cabin.charge,integral_prod _ ((hg.mono' (hm _ h.inside) (hG.mono fun i hi => hi _ h.inside)).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine (h.clean.exchange _ _ _ (h.pos _ h.inside _) (fun y => c * leftDerivs (C.cross F (x,y)) l U)
    (((h.packed l hl).comp measurable_prodMk_left).const_mul c) ?_).2
  exact fun y hy => not_not.mp fun hx => hy ((h.collar (x,y) l hl (right_ne_zero_of_mul hx)).self_of_nhds)

set_option maxHeartbeats 500000 in
lemma meas {c : ℂ} {l : List (Directions G n)} (hl : l.length ≤ k) (ht : Measurable (fun y:T.tag × T.Play => T.warm U y.1 y.2))
    (hh : Measurable (C.shift · U)) (hv : Measurable (C.copy · U)) (hp : Measurable (fun y : T.tag × T.Play => C.pin.faceFee (T.cov U y.1)
      (C.shift y.1 U) (T.warm U y.1 y.2))) : Measurable (uncurry (C.post F c U l)) := by
  let f (q:T.tag × T.Play) := C.pin.fetch (C.shift q.1 U) (C.copy q.1 U) (T.warm U q.1 q.2)
  have h1 : Measurable f := by
    have he:=C.pin.switch.measurable.comp ht
    have hg : Measurable (fun q:T.tag×T.Play => displaced (C.shift q.1 U) C.pin.g (C.pin.switch (T.warm U q.1 q.2)).2) :=
      tape.measurable.comp ((hh.comp measurable_fst).add ((measurable_snd.comp he).const_smul C.pin.g))
    refine (measurable_fst.comp he).prodMk (measurable_pi_lambda _ fun i => ?_)
    change Measurable (fun q:T.tag×T.Play => G.lieExp _ * C.copy q.1 U i)
    have h1 := (G.lieExp_cont.measurable.comp ((measurable_pi_apply i).comp hg))
    have h2 : Measurable (fun q : T.tag×T.Play => C.copy q.1 U i) := ((measurable_pi_apply i).comp hv).comp measurable_fst
    exact h1.mul h2
  exact hp.smul (((h.packed l hl).comp (measurable_fst.prodMk h1)).const_mul c)

lemma norm_vacuum (x : T.tag) (z : T.Play) (c : ℂ) : ‖C.post F c U [] x z‖ = ‖c‖ * ‖F U x (T.warm U x z)‖ := by
  have ht := h.clean.ret_pinned _ (C.copy x U) _ (h.pos _ h.inside x) _ (h.protect U h.inside x) z
  change C.pin.faceFee _ _ _ • C.cross F (x,_) U = F U x (T.warm U x z) at ht
  change ‖C.pin.faceFee _ _ _ • (c * C.cross F _ U)‖ = _; rw [←ht,Complex.real_smul,Complex.real_smul,mul_left_comm,norm_mul]; rfl
end Around
end Cabin
end YM.ProofPorts.CommonComplexProduction
