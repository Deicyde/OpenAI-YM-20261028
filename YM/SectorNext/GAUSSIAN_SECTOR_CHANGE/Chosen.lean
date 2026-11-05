import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Tier
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Windows



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Choices of C and μ for the actual integral

Use selected `move` A and boundary rows. Window here taken by the
symmetric option **whole endpoints** (max d_L of all projected
endpoints in the pair) instead of doubled cover midpoints: differs
from the initial-site metric by at most 2, uses exact oriented addresses.
We don't assert coincidence of the two prescriptions; theorem also
buys ANY windows containing the indicated smaller balls (if wishing to
use E midpoint implementation prove distance-to-parent within bounded
shift). Same rate & gap across placements, includes identity mode
completions (separate file checks), finite-range by construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented 
open Wisps Tier Schur LocalJet
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

def points (S : StepData c f) (i : Bond f) : Set (Site c) := {S.ratio.parent i.1,S.ratio.parent (i.1+Lattice.step i.2)}

def meeting (S : StepData c f) (x : ℝ) (i j : Bond f) : Prop :=
    ∀ y∈points S i,∀ z∈points S j,separation y z ≤ radiusB x / 20

def panels (A : Stores S) (F : Forest S.ratio) (i : In x A F (G:=G)) :=
  {j : In x A F (G:=G) | meeting S x i.1.val.val j.1.val.val}

lemma meetings (e : Bond f) {p : Site c} (h : p∈points S e) : separation (S.ratio.parent e.1) p ≤ 1 := by
  rw [points,Set.mem_insert_iff,Set.mem_singleton_iff] at h
  rcases h with h|h <;> rw [h]
  · simp
  · exact Work.E03.parent_step ..

lemma boards (A : Stores S) (F : Forest S.ratio) (G : Gauge) (h : 120 ≤ radiusB x) :
    Bars (panels (x:=x) A F (G:=G)) (front A F) (radiusB x / 60) := by
  intro i j he y hy z hz
  have hv := meetings _ hy
  have hp := meetings _ hz
  let u := front A F i; let v := front A F j
  apply (separation_triangle y v z).trans
  apply (Nat.add_le_add ((separation_triangle y u v).trans (Nat.add_le_add (show separation y u ≤ 1 from (separation_comm ..).trans_le hv) he)) hp).trans
  omega

/-- Check this prescription is *symmetric*, even on crossing bonds and
around the period seam under axis sign changes. -/
lemma meeting_comm (i j : Bond f) : meeting S x i j ↔ meeting S x j i := by
  constructor <;> intro h y hy z hz <;> exact (separation_comm ..).trans_le (h z hz y hy)





def fog (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) :=
  clouded (panels A F) (Rows.gram T x V k (shots S x) A F)

def meanLog (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) :=
  -(per (panels A F) (Rows.gram T x V k (shots S x) A F)).transpose *ᵥ blame T x V k (shots S x) A F q d Y

lemma meanLog_cont (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (q : Chi) (d : ℝ) {P : Teller G} (hT : P.Funds S T) (hd : 0<d) (ht : 2*d < firstRadius G) : Continuous (meanLog A F T x V k q d) := by
  obtain ⟨l,m,H,-⟩ := hT.feeds
  have hm := source_continuous T x V k (shots S x) A F q d H hd ht
  unfold meanLog blame mulVec dotProduct
  apply continuous_pi; intro i
  have hf j := (continuous_apply j).comp hm
  fun_prop

lemma fog_zero (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (i j : In x A F (G:=G)) (h : ¬ meeting S x i.1.val.val j.1.val.val) : fog A F T x V k i j=0 := by
  let L := per (panels A F) (Rows.gram T x V k (shots S x) A F)
  change (1/2:ℝ)*(L i j + L j i)=0
  rw [show L i j=0 from per_zero (panels A F) _ (mt (meeting_comm ..).mp h),
    show L j i=0 from per_zero (panels A F) _ h]; ring

private lemma delay {E δ : ℝ} (hd : 0 < δ) (G : Gauge) : ∀ᶠ x : ℝ in atTop, E*temp x ≤ δ := by
  have h0 := Work.E01.fiery_le G (1:Side) E
  filter_upwards [h0, (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hd)] with x hx he
  simpa [fiery,betaF] using hx.trans he

/-- Exact μ
also supported when put under `Change`.

Here A can include wrong
fine costs/noise entries (just ask output flags). -/
lemma opaqueCost (G : Gauge) (P : Patch) (Pt : Teller G) (hB : P.Branches Pt.bind G) :
    ∃ v K η b E : ℝ, 0<v ∧ 0 ≤ K ∧ 0<η ∧ 0<b ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    let U := Rows.gram T x V k (shots S x) A F
    Pours U (front A F) (front A F) v K ∧ Gapped U η ∧ U.PosDef ∧
      Pours (fog A F T x V k - U⁻¹) (front A F) (front A F) 0 (E*rate (-b) (radiusB x/60)) ∧
      (fog A F T x V k).PosDef := by
  obtain ⟨η,hη,Hg⟩ := Gap.not_flat G P Pt hB
  obtain ⟨C,δ,hC,hδ,H⟩ := written Pt.bind P G Pt hB
  let u := Pt.top.width; let v := u/2
  have hv : 0<u := Pt.top.width_pos
  have ht : 0<v := half_pos hv
  let key (v:ℝ) := ((Fintype.card G.ColorIndex:ℝ)*(Fintype.card (Site P.L)*Fintype.card Axis))*wealth v
  have hk v : 0 ≤ key v := by unfold key; have := wealth_nn v; positivity
  let α := max (Fintype.card G.ColorIndex * ((Fintype.card Signed:ℝ)*
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site P.L) * wealth v)+
      Fintype.card Axis * wealth v))) (key v) * C
  have ha : 0 ≤ α := mul_nonneg ((hk _).trans (le_max_right ..)) hC
  let D := α*α
  obtain ⟨b,E,g,hb,hE,hg,hW⟩ := Schur.windows ht hη (K:=D) (mul_nonneg ha ha) key hk
  have hr : Tendsto (fun x => radiusB x / 60) atTop atTop := by
    apply Filter.tendsto_atTop.mpr; intro i
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x hx; omega
  refine ⟨v,D,η,b,E,ht,mul_nonneg ha ha,hη,hb,hE,?_⟩
  filter_upwards [hr.eventually hW, Hg,delay (E:=permit P) hδ G, small_span P,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+120)] with x hx h hP hS h₀
  intro c f S T hs hl hT A F k V hV U
  have hj : Fintype.card (Site S.patch.L)=Fintype.card (Site P.L) := congr_arg (fun t : Patch => Fintype.card (Site t.L)) hs
  have hi (y : ℝ) : keyFee S G y = key y := by unfold keyFee key; rw [hj]
  have hh : Revenue (front A F (x:=x) (G:=G)) key := fun y hy i => (hi y) ▸ front_price y hy A F G i
  have he := H S T hs hT.knobs hT A V F x hV hS (by omega) (by omega) hP k
  have hd : max (slotFee S G v) (keyFee S G v)*C=α := by unfold slotFee; rw [hj,hi]
  have hm : Pours U (front A F) (front A F) v D := by
    have hy := pure hv hC he (down_price v ht S G) (front_price v ht A F G (x:=x))
    rw [hd] at hy
    exact hy.turn.fuse hy ht.le
  have hf : Gapped U η := by intro i; rw [sumSq_dot]; exact h S T hs hl hT A F k V hV i
  have hA : U.IsSymm := by unfold U Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  have ht := hx (front A F) U (panels A F) hh hm hA hf (boards A F G (by omega) (x:=x))
  exact ⟨hm,hf,dissolves hf hA hη,ht.1,ht.2.2⟩
end YM.Next.SectorChange
