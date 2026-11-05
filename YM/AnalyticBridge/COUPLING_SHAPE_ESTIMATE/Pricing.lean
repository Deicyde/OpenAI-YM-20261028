import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.CloverBill
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.PathPair
import YM.UVNext.PRICED_KERNELS.Degree
import YM.Work.A05.Window
import YM.Work.B09.Shell
import YM.Work.F05.Actions



/-! # True-length local bills for an unrotated path and its response. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG PathData Wilson Next.Scheduling.Wages UVNext.PricedKernels Work
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical
variable {G : Gauge} {n : Side} (P : PathData G) (c : Clip) (b : BudgetPoint)

private lemma same_inner (u : G.El) (x y : G.Color) : ⟪G.adjoint u x,G.adjoint u y⟫_ℝ=⟪x,y⟫_ℝ := by
  let L : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint u with norm_map' x := G.norm_adjoint u x }
  exact L.inner_map_map x y
lemma raw_symm (j : Sequence) : GaugeInvariant (raw (n:=n) P c j) := by
  intro u U; rcases j with ⟨x,_|⟨i,k⟩⟩
  · simp [raw,G.price_conj]
  simp only [raw,Sum.elim_inr,F05.slot_gauge,same_inner]
lemma response_symm (j : Sequence) : GaugeInvariant (response (n:=n) P c j) := by
  intro u U; rcases j with ⟨x,_|⟨i,k⟩⟩ <;> simp only [response, Sum.elim_inl,Sum.elim_inr,needles_mono,same_inner]

private lemma path_local (s : Slot) {X : Support n} (hs : walkCuts s 0 ⊆ X) : LocalOn (X:Set (Site n)) (fun U : Config G n => s.atSite U 0) := by
  intro U V h; apply LocalOn.expandAt _ _ s.covered
  refine agrees_mono h ?_
  rintro _ ⟨y,hy,rfl⟩; exact hs (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
lemma link_price (i : PlaqAxes) : LocalOn (ringlet (0:Site n)) (fun U : Config G n => faceValue U (directWord i)) :=
  fun U V h => travel_local _ _ U V fun e ha hb => h e (local_square (directWord i) (List.mem_toFinset.mpr ha))
      (local_square (directWord i) (List.mem_toFinset.mpr hb))

lemma zone_left (x : PlaqAxes) (d : ℕ × ℕ) : walkCuts (first P x d.1) 0 ⊆ imageOf (n:=n) P b (x,Sum.inr d) :=
  Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
lemma zone_right (x : PlaqAxes) (d : ℕ × ℕ) : walkCuts (first P x d.2) 0 ⊆ imageOf (n:=n) P b (x,Sum.inr d) := Finset.subset_union_right
lemma raw_local (j : Sequence) : LocalOn (imageOf (n:=n) P b j) (raw (n:=n) P c j) := by
  intro U V hh; rcases j with ⟨x,_ | d ⟩
  · simp only [raw,Sum.elim_inl, link_price x U V hh]
  have hl := path_local _ (zone_left (n:=n) P b x d) U V hh
  have hr := path_local _ (zone_right (n:=n) P b x d) U V hh
  simp only [raw,Sum.elim_inr,hl,hr]
lemma response_local (j : Sequence) : LocalOn (ringlet (0:Site n)) (response (n:=n) P c j) := by
  intro U V h; have he:=needles_local 0 U V h; simp only [response,he]
lemma raw_cont (j : Sequence) : Continuous (raw (n:=n) P c j) := by
  rcases j with ⟨x,_|⟨i,k⟩⟩
  · unfold raw; simp only [Sum.elim_inl]; unfold faceValue; fun_prop
  unfold raw; simp only [Sum.elim_inr]; unfold Slot.atSite expandAt; fun_prop
lemma response_cont (j : Sequence) : Continuous (response (n:=n) P c j) := by
  have hh (i:PlaqAxes) := continuous_pi_iff.mp (needles_cont (G:=G) (0:Site n)) i
  rcases j with ⟨x,_|⟨i,k⟩⟩ <;> exact continuous_const.mul ((hh _).inner (hh _))

private lemma path_bill (x : Slot) (X : Support n) (hs : walkCuts x 0⊆X) :
    bill b.order (b.dirBound (n:=n) 0) (Healthy b.threshold X) (slotCost G b.power b.order x.length * b.threshold)
      (fun U : Config G n => x.atSite U 0) := by
  have h := slotPays (G:=G) x x.stencil (Finset.Subset.refl _) _ le_rfl (0:Site n) b
  exact ⟨h.smooth,h.nonneg,fun W hl ht U he => h.bound W hl ht U (Disjoint.mono_left hs he)⟩

section
attribute [local instance] Gauge.frobInner

def spoke (G : Gauge) (b : BudgetPoint) := 2^b.order * ‖innerSL ℝ (E:=G.Mat)‖
def wireS (G : Gauge) (b : BudgetPoint) := 2^b.order * ‖innerSL ℝ (E:=G.Color)‖

def modulus (G : Gauge) (c : Clip) := weight*c.direct / (2*G.colorScale^2)
lemma modulus_pos (G : Gauge) (c : Clip) : 0 < modulus G c := div_pos (mul_pos weight_pos c.quadratic_pos) (by positivity [G.colorScale_pos])

/-- Factor `threshold²` priced separately. -/
def priceRaw (j : Sequence) := j.2.elim
  (fun _ => modulus G c * spoke G b * feeWalk G 4 b.power b.order ^2)
  (fun d => |copper P j.1 d| * wireS G b * slotCost G b.power b.order (first P j.1 d.1).length *
    slotCost G b.power b.order (first P j.1 d.2).length)

def priceResponse (j : Sequence) := j.2.elim
  (fun _ => weight*c.direct/2 * wireS G b * leafPrice G b ^2)
  (fun d => |copper P j.1 d| * wireS G b * leafPrice G b ^2)

private lemma ray_price (F : PathData G) (x : PlaqAxes) (w : Unit) (U : Config G n) :
    raw F c (x,Sum.inl w) U=modulus G c * ‖wordStamp 0 (square x.val.1 x.val.2) U‖^2 := by
  have hc := G.colorScale_pos
  let W:=faceValue U (directWord x); have he:=G.chord_price W
  change (‖wordStamp 0 (square x.val.1 x.val.2) U‖/G.colorScale)^2=2*G.price W at he
  change weight*c.direct*G.price W = _; unfold modulus; field_simp at *; rw [he]; ring

lemma bill_raw (j : Sequence) : bill (G:=G) b.order (b.dirBound (n:=n) 0) (Healthy b.threshold (imageOf P b j))
    (priceRaw P c b j*b.threshold^2) (raw P c j) := by
  rcases j with ⟨x, w|d⟩
  · let l:=square x.val.1 x.val.2; let Z:=Healthy (G:=G) b.threshold (ringlet (0:Site n))
    have h := word_fund 0 l b Z fun U hu => local_chord hu (directWord x) (central 0)
    have he:=bill_scalar (modulus G c) (bill_pair h h (innerSL ℝ))
    rw [abs_of_pos (modulus_pos G c)] at he
    have hz : raw (n:=n) P c (x,Sum.inl w)=(fun U=> (modulus G c) • inner ℝ (wordStamp 0 l U) (wordStamp 0 l U)) := by
      funext U
      rw [ray_price,real_inner_self_eq_norm_sq]; rfl
    rw [hz]
    convert he using 1 <;> try rfl
    simp only [priceRaw,Sum.elim_inl,spoke,show l.length=4 from rfl]; ring
  let Z:=imageOf (n:=n) P b (x,Sum.inr d)
  have he := bill_scalar (copper P x d) (bill_pair (path_bill (G:=G) b _ Z (zone_left ..)) (path_bill b _ Z (zone_right ..)) (innerSL ℝ))
  convert he using 1 <;> try rfl
  simp only [priceRaw, Sum.elim_inr,wireS]; ring

lemma bill_response (j : Sequence) : bill (G:=G) b.order (b.dirBound (n:=n) 0) (Healthy b.threshold (ringlet 0))
    (priceResponse P c b j*b.threshold^2) (response P c j) := by
  rcases j with ⟨x, w|d⟩
  · have h := thorn_bill (G:=G) x b (0:Site n); have he:=bill_scalar (weight*c.direct/2) (bill_pair h h (innerSL ℝ))
    convert he using 1 <;> try rfl
    simp only [priceResponse,Sum.elim_inl,wireS,abs_of_nonneg (by positivity [weight_pos,c.quadratic_pos] : 0≤weight*c.direct/2)]; ring
  have he := bill_scalar (copper P x d) (bill_pair (thorn_bill (G:=G) (first P x d.1).plaq b (0:Site n))
    (thorn_bill (G:=G) (first P x d.2).plaq b (0:Site n)) (innerSL ℝ))
  convert he using 1 <;> try rfl
  simp only [priceResponse,Sum.elim_inr,wireS]; ring
end

lemma raw_reg (j : Sequence) : b.Regular (n:=n) (imageOf P b j) (raw (n:=n) P c j) :=
    reg_bill b _ (raw_local P c b j) (raw_cont P c j) (raw_symm P c j) (bill_raw ..)
lemma response_reg (j : Sequence) : b.Regular (n:=n) (ringlet 0) (response P c j) :=
    reg_bill b _ (response_local P c j) (response_cont P c j) (response_symm P c j) (bill_response ..)
end YM.AnalyticBridge.CouplingShape
