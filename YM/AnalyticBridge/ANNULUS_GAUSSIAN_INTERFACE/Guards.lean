import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Geometry

set_option warningAsError false

/-!
# Protected packet eligibility, on the profiles allocation

Split on the actual tags once, relative to
uniform *prior on tags*. D=200 gives the 300-halo convention; here
include also the (scaled-to-uniform-tags) likelihoods through that
halo. Keep other factors verbatim, not *assuming* likelihood ratios
out there are always one. Flags test incidence at any of the touched
sites. All formulas apply to one U (even with defaults not met outside
these locations). `Chi.profiles` chosen; don't claim pointwise
factorization into local tables for arbitrary global allocations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
  YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}

structure Visits (S : StepData c f) where
  sites : Finset (Site c)
  faces : Finset (Cell f)
  bonds : Finset (Bond c)

namespace Visits
variable (O : Stores S)

def near (D : ℕ) (x : ℝ) : Visits S :=
  let H := O.dome ((D+100)*radiusB x)
  ⟨H,Finset.univ.filter fun p => ¬ Disjoint H (startPos S p),
    Finset.univ.filter fun i => ¬ Disjoint H (pinPos i)⟩

def unattended (w : Visits S) : Visits S := ⟨w.sitesᶜ,w.facesᶜ,w.bondsᶜ⟩ -- visits outside, not *ignored*
end Visits

namespace Seed
variable {ι : Type*} [DecidableEq ι] (q : Chi)

def piece (s : Finset ι) (d x : ℝ) (i : ι) := if i∈s then 1 - q.innerShare d x else q.innerShare d x



lemma piece_range (s : Finset ι) (d x : ℝ) (i : ι) : piece q s d x i ∈ Icc 0 1 := by
  have hf : q.innerShare d x ∈ Icc 0 1 := q.range _
  unfold piece; split
  · exact ⟨sub_nonneg.mpr hf.2, sub_le_self _ hf.1⟩
  exact hf

lemma relevance (s : Finset ι) {d x : ℝ} {i : ι} (h : piece q s d x i ≠ 0)
    (hd : 0<d) (hr : 0≤x) : (i∈s → d<x) ∧ (i∉s → x<2*d) := by
  unfold piece at h
  exact ⟨fun ha => q.exterior_gt _ _ hr hd (by rwa [if_pos ha] at h),
    fun ha => q.chosen_lt _ _ hd (by rwa [if_neg ha] at h)⟩
end Seed

/-- Literal output-flag predicate at each queried site. -/
def flagCharge (A : Stores S) (x : ℝ) (V : Config G c) (i : Site c) : ℝ :=
  if (i∈A.flags ↔ i∈RG.flags (temp x) V) then 1 else 0

def border (X : Visits S) (A : Stores S) (q : Chi) (x w : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) :=
    (∏ i∈X.sites, flagCharge A x V i)*
      ((∏ p∈X.faces, Seed.piece q A.costs (fiery G x S.patch.L/4) (toll U p) p)*
        ∏ b∈X.bonds, Seed.piece q A.aisles (w*fiery G x S.patch.L) (wire (S.prediction U k) V b) b)

lemma border_range (X : Visits S) (A : Stores S) (q : Chi) (x w : ℝ)
    (U : Config G f) (V : Config G c) (k : S.Choices) : border X A q x w U V k ∈ Icc 0 1 := by
  have h {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : ∀ i, f i ∈ Icc 0 1) : (∏ i∈s,f i)∈ Icc 0 1 :=
    ⟨Finset.prod_nonneg fun i _ => (h i).1,
      le_trans (Finset.prod_le_prod (fun i _ => (h i).1) (fun i _ => (h i).2)) (by simp)⟩
  have he {a b : ℝ} (h : a ∈ Icc 0 1) (he : b∈ Icc 0 1) : a*b∈ Icc 0 1 :=
    ⟨mul_nonneg h.1 he.1,(mul_le_mul h.2 he.2 he.1 zero_le_one).trans (by simp)⟩
  exact he (h _ _ fun i => by unfold flagCharge; split <;> simp) (he (h _ _ fun _ => Seed.piece_range ..) (h _ _ fun _ => Seed.piece_range ..))



def frameRate (S : StepData c f) (k : S.Choices) (U : Config G f) (i : Site c) :=
    Fintype.card S.patch.FrameTag * S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i)

def bondRate (S : StepData c f) (k : S.Choices) (U : Config G f) (i : Bond c) :=
    Fintype.card S.patch.Points * S.patch.predictorMass S.kernel (S.connector U k.1 i) (k.2 i)

def tagRate (X : Visits S) (k : S.Choices) (U : Config G f) :=
    (∏ i∈X.sites, frameRate S k U i) * (∏ i∈X.bonds,bondRate S k U i)

lemma frame_zero (i : Site c) (k : S.Choices) (U : Config G f) : 0≤S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i) := by
  unfold frameMass; split
  · positivity
  split <;> positivity
lemma bond_zero (i : Bond c) (k : S.Choices) (U : Config G f) : 0≤S.patch.predictorMass S.kernel (S.connector U k.1 i) (k.2 i) := by
  unfold predictorMass; split
  · positivity
  exact weight_nonneg ..

lemma rate_cost (X : Visits S) (k : S.Choices) (U : Config G f) :
    tagRate X k U ∈ Icc 0 ((Fintype.card S.patch.FrameTag:ℝ)^X.sites.card*(Fintype.card S.patch.Points:ℝ)^X.bonds.card) := by
  have he i : frameRate S k U i ∈ Icc 0 (Fintype.card S.patch.FrameTag:ℝ) := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (frame_zero i ..),mul_le_of_le_one_right (Nat.cast_nonneg _) ?_⟩
    unfold frameMass; split
    · exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr Fintype.card_pos)
    split <;> rename_i he
    · exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨_,he⟩))
    exact zero_le_one
  have hl i : bondRate S k U i ∈ Icc 0 (Fintype.card S.patch.Points:ℝ) := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (bond_zero i ..),mul_le_of_le_one_right (Nat.cast_nonneg _) ?_⟩
    unfold predictorMass; split
    · exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr Fintype.card_pos)
    exact le_trans (Finset.single_le_sum (fun i _ => S.patch.weight_nonneg i) (Finset.mem_univ _)) S.patch.weight_sum.le
  have h {ι : Type} (s : Finset ι) (f : ι → ℝ) {E : ℝ} (h : ∀ i, f i ∈ Icc 0 E) :
      (∏ i∈s,f i)∈ Icc 0 (E^s.card) :=
    ⟨Finset.prod_nonneg fun i _ => (h i).1,
      le_trans (Finset.prod_le_prod (fun i _ => (h i).1) (fun i _ => (h i).2)) (by simp)⟩
  obtain ⟨ha,hb⟩ := h X.sites _ he
  obtain ⟨hc,hd⟩ := h X.bonds _ hl
  exact ⟨mul_nonneg ha hc,mul_le_mul hb hd hc (ha.trans hb)⟩



private lemma spin_rate (i : Site c) (s : Signed) (k : S.Choices) (U : Config G f)
    (h : S.patch.Branches S.kernel G) : frameRate S k U (s.act i)=frameRate S (choice s k) (pull s 0 U) i := by
  let t := choice s k
  have he : k=S.withinChoice s 0 t := ((S.withinChoice s 0).apply_symm_apply k).symm
  have hx : S.ratio.embed 0=0 := S.ratio.root.map_zero
  unfold frameRate; apply congr_arg
  change S.patch.frameMass S.kernel (expandAt (S.ratio.embed (s.act i)) U) (k.1 (s.act i)) =
    S.patch.frameMass S.kernel _ (t.1 i)
  have hj : k.1 (s.act i) = S.patch.orient s (t.1 i) := by
    have h0 : k.1=S.withinSites s 0 t.1 := congr_arg Prod.fst he
    rw [h0]; simpa only [affine,add_zero] using S.port_site s 0 t.1 i
  rw [hj,← hx,expandAt_pull, S.port]
  have hv := (S.patch.frames_channel h s (expandAt (S.ratio.embed (s.act i)) U) (t.1 i)).1.symm
  simp only [affine,add_zero]; exact hv

private lemma necessary {ι : Type} [DecidableEq ι] {X : Finset ι} {f : ι → ℝ} (h : (∏ i∈X, f i) ≠ 0) (i : ι) (hi : i∈X) : f i ≠ 0 :=
    fun he => h (Finset.prod_eq_zero hi he)

/-- All orientation-local `Plot`-like prerequisites for affine-core
payment. Nonzero real profiles retained on numerical and guard halos,
not integrability alone. -/
lemma posted (O A : Stores S) (q : Chi) (D : ℕ) (x w : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices)
    (hw : 0<w) (ht : 0<fiery G x S.patch.L) (hb : S.patch.Branches S.kernel G) :
    let X := Visits.near O D x
    border X A q x w U V k * tagRate X k U ≠ 0 →
    ∀ s, Wide (turnStore s O) (turnStore s A) D x w (pull s 0 U) (choice s k) (pull s 0 V) := by
  intro X he s
  have h0 := left_ne_zero_of_mul he
  have hl := right_ne_zero_of_mul he
  have hn := right_ne_zero_of_mul h0
  have ha {i : Site c} (h : i∈(turnStore s O).dome ((D+5)*radiusB x)) : s.act i ∈ X.sites := expand_dome O
    (show (D+5)*radiusB x ≤ (D+100)*radiusB x from Nat.mul_le_mul_right _ (by omega)) ((turn_dome ..).mp h)
  constructor
  · intro p hi
    obtain ⟨i,hx,hy⟩ := Finset.not_disjoint_iff.mp hi
    let j := Oriented.faces s f p
    have hJ : j∈X.faces := by
      apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,Finset.not_disjoint_iff.mpr ⟨_,ha hx,?_⟩⟩
      unfold j; rw [start_send]; exact Finset.mem_image_of_mem _ hy
    have h := necessary (left_ne_zero_of_mul hn) j hJ
    obtain ⟨h1,h2⟩ := Seed.relevance q A.costs h (by positivity) (G.chord_nonneg _)
    have hz : toll (pull s 0 U) p=toll U j := Face.send_price U p s 0 G.chord G.chord_inv fun k g => G.chord_conj g k
    rw [turn_costs,hz]; exact ⟨fun hg => (h1 hg).le, fun hg => by linarith [h2 hg]⟩
  · intro p hi
    obtain ⟨i,hx,hy⟩ := Finset.not_disjoint_iff.mp hi
    let j := sendEdge s 0 p
    have hJ : j∈X.bonds := by
      apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, Finset.not_disjoint_iff.mpr ⟨_,ha hx,?_⟩⟩
      unfold j; rw [pin_send]; exact Finset.mem_image_of_mem _ hy
    have h := necessary (right_ne_zero_of_mul hn) j hJ
    obtain ⟨h1,h2⟩ := Seed.relevance q A.aisles h (by positivity) (G.chord_nonneg _)
    rw [turn_aisles,(carry s hb k U).2,wire_pulled]
    refine ⟨fun hg => (h1 hg).le,fun hg => (h2 hg).le.trans_eq ?_⟩; ring
  · intro i hi
    rw [turn_flags,turn_flag_actual]; have hz := necessary (left_ne_zero_of_mul h0) (s.act i) (ha hi)
    unfold flagCharge at hz; split at hz
    · assumption
    exact (hz rfl).elim
  · intro i hi
    have hz := necessary (left_ne_zero_of_mul hl) (s.act i) (ha hi)
    rw [spin_rate _ s _ _ hb] at hz
    exact lt_of_le_of_ne (frame_zero i _ _) (Ne.symm (right_ne_zero_of_mul hz))



end YM.AnalyticBridge.Annulus
