import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Narrow
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Receiving
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StampQ
import YM.Push.GRID_APPROXIMATION.Cone


/-!
# Non-warning dictionary

Before regrouping. Addresses deterministic; halo parameter l for all
optional footprints. E extensions simple value h even on hull-remote; no
field derivatives of hard indicators. Psi stencil from actual possible
U-reads (can suppress outside via ignored choice). Later overlap by support
which retains these augmented and all queries. f-sector cores don't count
columns from independent tables. R positive physical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ K : ℝ} {η r Q Y : ℝ} {L : Side}

namespace Coat
variable (X : Coat T F)

/-- old path read. Post l=0 only for accessing chart links. Don't use l=0
for the pricing. -/
def inhale (R : Rep G f) (a : ℝ) (U : Directions G f) (p : Raw.LogLetter c f) :=
    Raw.expo T X.x R (X.input U) X.V p * X.enforce (2*a) U (X.plaza (Raw.space T 0 X.B R p))

/-- full footprints price of h, not just selected emit operations. -/
def bag (R : Rep G f) (a : ℝ) (U : Directions G f) (p : ℕ) :=
    R.activities.K p (X.input U)*X.enforce (2*a) U (X.plaza (Raw.forcedFoot S.ratio 0 X.B R p))

/-- Raw `LogLetters` included, fine-scale. Cn mask effective and retained;
k siblings numeric multiplies budgeted separately. -/
abbrev ChainIndex (f : Side) := Ledger f 3 ⊕ Ledger f 3 ⊕ Ledger f 1 ⊕ Bond f ⊕ Ledger f 2
abbrev LogIndex (c f : Side) := Raw.LogLetter c f ⊕ Miniature c f ⊕ ChainIndex f

def basisFoot (S : StepData c f) (B l : ℕ) : ChainIndex f → Support c :=
    Sum.elim (receipt S B l 3) (Sum.elim (receipt S B l 3)
    (Sum.elim (receipt S B l 1) (Sum.elim (town S B l) (receipt S B l 2))))
def basisCharge (f : Side) : ChainIndex f → ℕ :=
    Sum.elim Sigma.fst (Sum.elim Sigma.fst (Sum.elim Sigma.fst (Sum.elim (fun _ => 0) Sigma.fst)))
def roadway (T : Tube G S) (R : Rep G f) (B l : ℕ) : LogIndex c f → Support c :=
    Sum.elim (Raw.space T l B R) (Sum.elim (sleeve S B l) (basisFoot S B l))
def exCharge (T : Tube G S) (R : Rep G f) : LogIndex c f → ℕ :=
    Sum.elim (Raw.extra T R) (Sum.elim (fun _ => 0) (basisCharge f))

def fuel (a β : ℝ) (z : Air f G) : ChainIndex f → ℝ :=
    let G := X.plate; let D := X.shutter
    Sum.elim (fun i => -(ArmA D G i)/2)
    (Sum.elim (fun i => ArmA D X.blank.plate i/2)
    (Sum.elim (fun i => ArmS D G i/2) (Sum.elim (X.qfirst β z a) (X.chain β z a))))

def farLog (R : Rep G f) (a : ℝ) (Ñ : ChartRatio G) (z : Air f G) : LogIndex c f → ℝ :=
    let u := X.liftA R.beta z
    Sum.elim (X.inhale R a u) (Sum.elim (X.Short u Ñ R.beta a) (X.fuel a R.beta z))

def raiseAir (R : Rep G f) (a : ℝ) (Ñ : ChartRatio G) (z : Air f G) (p : LogIndex c f) :=
    Real.exp (X.farLog R a Ñ z p)-1

lemma smallCensus (S : StepData c f) (L : Side) (h : S.patch.L=L) :
    Census (Fintype.card Signed*Census.spots L+(Itinerary.density L+Itinerary.density L)) (caption S) := by
  rw [← h]; apply Census.added _ (Census.added (perch S) (perch S)); apply prefix_counts (p:=fun i j=> rowSite S (i,j))
  intro i; exact (anchors S).permute i.actEquiv.toEquiv
lemma packed (S : StepData c f) {B l : ℕ} (hp : 0<B) (p : Miniature c f) : sleeve S B l p ⊆ Animals.neighbors ((l+1)*B) (caption S p) := by
  intro v hi; apply (Animals.neighbors_mem ..).mpr
  rcases p with p|p|p <;> rw [Nat.add_mul,one_mul]
  · exact ((Animals.neighbors_mem ..).mp hi).trans (by omega)
  · exact (checking _ _ _ _ _ hi).trans (by omega)
  exact (checking _ _ _ _ _ hi).trans (by omega)
lemma exChart (S : StepData c f) (T : Tube G S) (R : Rep G f) (B l : ℕ) (p : LogIndex c f) :
    (roadway T R B l p).Nonempty := by
  rcases p with p|p
  · exact Raw.space_ne ..
  rcases p with (p|p|p) | (p|p|p|p|p)
  · exact ⟨rowSite S p,(Animals.neighbors_mem ..).mpr (by rw [separation_self]; omega)⟩
  · exact ⟨_,city S l B p⟩
  · exact ⟨_,city S l B p⟩
  · exact ⟨_,cities S l B p.2.1 p.2.2⟩
  · exact ⟨_,cities S l B p.2.1 p.2.2⟩
  · exact ⟨_,cities S l B p.2.1 p.2.2⟩
  · exact ⟨_,city S l B p⟩
  exact ⟨_,cities S l B p.2.1 p.2.2⟩

/-- Remaining address after signs/germs but before exponentiating. Includes explicit
income on LogGas. Assumed `Allow` for BOTH flat with same T,H,W,etc and
all real points (choose shoots universally once). General per-Coat but
X independence via pricing before forall. -/
structure Port (P : Teller G) (L : Side) (η r Q Y : ℝ) (X : Coat T F) : Prop where
  sails : Rotator P L η r Q Y X
  empty : Rotator P L η r Q Y X.blank
  allgauge (z : Site c → G.El) : Rotator P L η r Q Y (X.rinse z)
  placed : X.manifest

section reach
variable {l : ℕ} {C a b ε : ℝ}

def specials (G : Gauge) (L : Side) (B : ℕ) (η r Q M J : ℝ) (S : StepData c f) : ChainIndex f → ℝ :=
    let u := Census.tubularPrice G L
    Sum.elim (Itinerary.capA G S η r Q u B) (Sum.elim (Itinerary.capA G S η r Q u B)
      (Sum.elim (Itinerary.capS G S η r Q u B) (Sum.elim (fun _ => J) (Coat.capQ S η r Q u B G M))))
lemma dynasty (P : Teller G) (L : Side) (h : Torch η r Q) (l : ℕ) (hh : 4 ≤ l) {W γ K C H Y b v ε : ℝ}
    (hp : 0<H) (hc : 0<C) {E : ℝ → ℝ} (he : Rate G L (b-1/2) E) (hn : 0≤v) :
    ∃ M J A : ℝ→ℝ, Rate G L b A ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
     (F : Forest S.ratio) (X : Coat T F), X.x=x → S.patch.L=L → Port P L η r Q Y X → Tender x W γ K C (|E x|) X →
       let z := specials G L (radiusB x) η r Q (M x) (J x) S
       Sales (radiusB x) v ε (basisFoot S (radiusB x) l) z (basisCharge f) (A x) ∧
       ∀ β>0, β≤ 2*betaF G x L → ∀ w i, |X.fuel H β w i| ≤ z i := by
  obtain ⟨M,J,U,V,hM,hJ,hU,hV,H₁⟩ := sellers (W:=W) (A:=v) (γ:=γ) (K:=K) (Y:=Y) P L h l hh hn hp hc (ε:=ε) he
  obtain ⟨A,Z,hA,hZ,H₂⟩ := Itinerary.quoted P L h l hh v ε b Y hn
  refine ⟨M,J,_,hA.add (hA.add (hZ.add (hV.add hU))),?_⟩
  filter_upwards [H₁,H₂] with x hx hh c f S T F X hX hL hP ht z
  obtain ⟨h₁,h₂,h₃⟩ := hx c f S T F X hX hL hP.sails ht
  obtain ⟨h₄,h₅,h₆,h₇⟩ := hh c f S T F X hX hL hP.sails
  obtain ⟨-, -, h₈, -⟩ := hh c f S T F X.blank hX hL hP.empty
  subst x
  refine ⟨h₄.together (h₄.together (h₅.together (h₂.together h₁))), fun β hb hx w i => ?_⟩
  rcases i with i|i|i|i|i
  · have he := h₆ i; unfold fuel; dsimp only [Sum.elim]; rw [abs_div,abs_neg]; apply le_trans _ he; exact div_le_self (abs_nonneg _) (by norm_num)
  · have he := h₈ i; unfold fuel; dsimp only [Sum.elim]; rw [abs_div]; apply le_trans _ he; exact div_le_self (abs_nonneg _) (by norm_num)
  · have he := h₇ i; unfold fuel; dsimp only [Sum.elim]; rw [abs_div]; apply le_trans _ he; exact div_le_self (abs_nonneg _) (by norm_num)
  · exact (h₃ β hb hx w).2 i
  exact (h₃ β hb hx w).1 i

lemma minorizes (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (M V H : ℝ) (hM : 0<M) (hH : 0<H)
    (h : Torch η r Q) {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) (l : ℕ) (v ε : ℝ) (hV : 0≤v) :
    ∃ E J : ℝ→ℝ, Rate G L (-(1/2)) J ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
      (F : Forest S.ratio) (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Port P L η r Q V X → Stamp T →
      (∀ w, Maximum M T x w) → Sales (radiusB x) v ε (sleeve S (radiusB x) l) (fun _=>E x) (fun _=>0) (J x) ∧
      ∀ u i β, 0<β → β ≤ 2*betaF G x L → |X.Short u Ñ β H i| ≤ E x := by
  obtain ⟨E,hE,h⟩ := minute P L D hd M V H hM hH h hÑ
  let k := Fintype.card Signed*Census.spots L+(Itinerary.density L+Itinerary.density L)
  let J x := ((Animals.ballCost ((l+1)*radiusB x):ℝ)*k)*(E x*Real.exp (v*Animals.ballCost (l+1)))
  have hk := Census.width_rate G L (l+1) 0; simp only [add_zero] at hk
  have hp : Rate G L (-(1/2)) J := by convert ((hk.mul_right k).mul (hE.mul_right _)) using 1; ring
  refine ⟨E,J,hp,h.mono ?_⟩
  intro x hx c f S T F X hh hS hL hr hZ ha
  subst x
  obtain ⟨hw,h⟩ := hx _ _ _ _ F X rfl hS hL hr.sails hr.empty hr.allgauge hZ ha hr.placed
  have he : 0<X.B := lt_of_lt_of_le (by norm_num) hr.sails.room.sight.1
  exact ⟨fixed (smallCensus S L hL) he (sleeve S X.B l) (packed S he) hV hw, h⟩
end reach
end Coat
end YM.ConnectedActivityE6
