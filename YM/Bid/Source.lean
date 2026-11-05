import YM.PCalc.Band
import YM.Source.Drops

/-!
# Normalization: requests G01–G08 on Snap ≈ reference time origins.

Alternative section via analytic recovery from finitely many path curvature
factors. Need real projection & t^ell norm. G07 price kernel widths of that
alternate on finite stencils for actual Conv, not arbitrary clean.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Filter Function Set RG Wilson Lattice Supply Labels Source Drops InnerProductSpace MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal
variable {G : Gauge} {d : ℕ}

-- H exists genuinely. π not a field optimizer.

def swirls (H : Hol G) := ∀ (s : Signed) d (J : Jet G) t,
    pull s 0 (H.links d J t)=H.links d (changedJet (fun _ => Taylor.turn s.ortho⁻¹) J) t

def G01 : Prop := ∀ (G : Gauge) (H : Hol G), swirls H ∧ ∀ d v (u : G.El) (A : Snap G d), takes H d v (Cast u A)=G.adjoint u (takes H d v A)

/-- Joint analytic recovery for each Slot type. -/
def G02 : Prop := G01 → ∀ (G : Gauge) (H : Hol G) (d : ℕ), Peg H d

/-- Kernel of linearized jet sampler. Use `glow`! finite number of ANY
                    fundamental loops (claim unknown). -/
def G03 : Prop := ∀ (G : Gauge) (H : Hol G) (d : ℕ), Peg H d → ∃ (s : ℕ) (B : Fin s → Slot), lifts H d s B

structure Equivariant (H : Hol G) (d : ℕ) {m} (B : Fin m → Slot) : Prop where
  smooth : AnalyticAt ℝ (bring H d B) 0
  detects : ∃ C : GaugePanel G m →ₗ[ℝ] Snap G d, (∀ x, C (fderiv ℝ (bring H d B) 0 x)=x) ∧
                          ∀ u x,C (rotates u x)=Cast u (C x)

def G04 : Prop := ∀ (G : Gauge) (H : Hol G) (d m : ℕ) (B : Fin m → Slot), Peg H d → lifts H d m B → Equivariant H d B

-- Real polynomial on slots. Terms all length≥ l.
abbrev Pose (G : Gauge) (n : ℕ) := MvPolynomial (Fin n×G.ColorIndex) ℂ

def lows {n} (p : Pose G n) (i : ℕ) : Prop := ∀ m∈p.support,i ≤ m.sum fun _ j => j

def lumin {G : Gauge} {n} (p : Pose G n) (q : GaugePanel G n) := MvPolynomial.aeval (fun i : Fin n × G.ColorIndex => ((q i.1 i.2:ℝ):ℂ)) p

def mapped {s} (B : Fin s → Slot) (U : CoverConfig G) : GaugePanel G s := fun i => (B i).eval U

def Cumuli (H : Hol G) (d : ℕ) (F : Labels.Frame G d) {m} (B : Fin m → Slot) (P : F.Index → Pose G m) : Prop :=
    P 0=1 ∧ (∀ i u x, lumin (P i) (rotates u x)=lumin (P i) x) ∧ (∀ i x,star (lumin (P i) x)=lumin (P i) x) ∧
        (∀ i, Projects H (F.basis i) (lumin (P i) ∘ mapped B)) ∧ ∀ i,lows (P i) (F.grades i).2

def G05 : Prop := ∀ (G : Gauge) (H : Hol G) (d : ℕ) (F : Labels.Frame G d) (m : ℕ) (B : Fin m → Slot), Peg H d → ∀ f, Vision H d B f →
        ∃ P,Cumuli H d F B P

def pop {F : Labels.Frame G d} (T : SectionData F) := ∀ i : F.Index, ∃ (m : ℕ) (B : Fin m → Slot),
    (∀ b,(B b).stencil ⊆ T.stencil) ∧ ∃ P, T.evaluate (Pi.single i 1)=(lumin P ∘ mapped B (G:=G)) ∧ lows P (F.grades i).2

def G06 : Prop := ∀ (G : Gauge) (H : Hol G) (d : ℕ) (F : Labels.Frame G d) (m : ℕ) (B : Fin m → Slot),
    swirls H → (∃ P, Cumuli H d F B P) →
      ∃ T : SectionData F, T.Sound H ∧ pop T

/-- charged section, independent even support cost. Includes nonlinear part. -/
def Credit {F : Labels.Frame G d} (T : SectionData F) (k P : ℕ) (w : ℝ) :=
    ∀ B : BudgetPoint, B.order=k → B.power=P → ∀ n : Side, ∀ o : Site n, ∀ i : F.Index,
      B.Regular (T.footprint o) (T.places (Pi.single i 1) o) ∧
      B.supBounds o (T.footprint o) (T.places (Pi.single i 1) o) (w*B.threshold^(F.grades i).2)

def G07 : Prop := ∀ (G : Gauge) (H : Hol G) (d : ℕ) (F : Labels.Frame G d) (T : SectionData F), T.Sound H → pop T →
    ∀ k P : ℕ,∃ A : ℝ,Credit T k P A

-- smoke
structure Learns (G : Gauge) (H : Hol G) (F : Frames G) : Prop where
  builds : ∃ B : ∀ d : ℕ,SectionData (F.level d),(∀ d, (B d).Sound H) ∧ (∀ d,pop (B d)) ∧
    ∀ d k P, ∃ v,Credit (B d) k P v

set_option maxHeartbeats 400000 in
lemma teaching (G : Gauge) (H : Hol G) (F : Frames G) (a : G01) (b : G02) (c : G03) (d : G04) (e : G05) (f : G06) (v : G07) : Learns G H F := by
  classical
  have ht (i) : ∃ Q : SectionData (F.level i), Q.Sound H ∧ pop Q := by
    have hx := b a G H i
    obtain ⟨m,B,hB⟩ := c G H i hx
    obtain ⟨he,C,h1,h2⟩ := d G H i m B hx hB
    obtain ⟨u,hv⟩ := insight he C h1 h2 hx
    exact f G H i (F.level i) m B (a G H).1 (e G H i (F.level i) m B hx u hv)
  choose Q hB hc using ht
  exact ⟨Q,hB,hc,fun i k P => v G H i _ _ (hB i) (hc i) k P⟩
end YM.Bid
