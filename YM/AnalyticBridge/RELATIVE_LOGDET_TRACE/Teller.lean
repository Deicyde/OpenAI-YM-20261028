import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Papyrus
import YM.Push.FREE_RESOLVENT.BlockRate


/-!
# Precision inputs for differential marks

ONLY the fixed-sector derivative calculus uses the hypothesis on precision
jets (not a postulate about inverse or selected determinant); the actual finite
differences come from unconditional-on-jets input. Combine at the same torus,
using the same full keys, seed/table/actual V/G. All costs here in terms of
projected output. The orientation/field dependence licenses
on A (for derivatives with mask kept FIXED), when needed, must give
smoothness at the germ used on the chosen extension, not derivatives w.r.t.
the actual pushed flags at y.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Differential
open Function Filter Set Matrix MeasureTheory FreeResolvent TestD
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : E→Square ι} {x : E} {τ : Type*}
variable {D : Cost X} {v : τ→E} {G : Mark τ X} {p : ι→X} {W : ι→Set ι} {k : ℕ} {b C q R δ d U M V r s ε : ℝ}

/-- The one (decreased) rate we require for unprojected per occurrence
mark transfers. Can buy e.g. with radial or list geometry via Mark. -/
def cash (d : ℝ) (k : ℕ) := d/((2*k+1:ℕ):ℝ)
lemma cash_pos (k : ℕ) (hd : 0<d) : 0<cash d k := div_pos hd (by positivity)
lemma cash_bounds (k : ℕ) (hd : 0<d) : cash d k≤d ∧ (k+1:ℕ)*cash d k+k*cash d k ≤ d := by
  have ht := cash_pos k hd
  have he : cash d k * ((2*k+1:ℕ):ℝ)=d := div_mul_cancel₀ _ (by positivity)
  push_cast at *; have hn : 0≤(k:ℝ)*cash d k := by positivity
  constructor <;> linarith

omit [DecidableEq ι] [NormedSpace ℝ E] in
lemma holds (h : ContinuousAt A x) (he : Gap (A x) s) (d : ℝ) (hd : d<s) (D : Cost X) (p : ι→X) : ∀ᶠ y in 𝓝 x, Gap (A y) d := by
  let y := s-d
  have hh : 0< y := sub_pos.mpr hd
  let P a:= A a-A x
  have hp : ∀ᶠ a in 𝓝 x, D.Schur p p 0 y (P a) := by
    have hr (i) : ContinuousAt (fun a=>∑ j, |P a i j|) x := ((continuous_finsetSum _ fun j _ => ((continuous_id (X:=Square ι)).matrix_elem i j).abs).continuousAt).comp (h.sub continuousAt_const)
    have hc (j) : ContinuousAt (fun a=>∑ i, |P a i j|) x := ((continuous_finsetSum _ fun i _ => ((continuous_id (X:=Square ι)).matrix_elem i j).abs).continuousAt).comp (h.sub continuousAt_const)
    have hg (i : ι) := (hr i) (ge_mem_nhds (b:=∑ j,|P x i j|) (a:=y) (by simp only [P,sub_self,Matrix.zero_apply,abs_zero,Finset.sum_const_zero]; exact hh))
    have hv (j : ι) := (hc j) (ge_mem_nhds (b:=∑ i,|P x i j|) (a:=y) (by simp only [P,sub_self,Matrix.zero_apply,abs_zero,Finset.sum_const_zero]; exact hh))
    filter_upwards [show ∀ᶠ a in 𝓝 x, ∀ i, (∑ j, |P a i j|) ≤ y from eventually_all.mpr hg, show ∀ᶠ a in 𝓝 x, ∀ j, (∑ i, |P a i j|) ≤ y from eventually_all.mpr hv] with a ha hb
    constructor <;> constructor <;> intro i
    · simpa only [Cost.weight_zero,one_mul] using ha i
    simpa only [Cost.weight_zero,one_mul,Matrix.transpose_apply] using hb i
  exact hp.mono fun a ha => (he.perturb ha).mono (by unfold y; linarith)

omit [DecidableEq ι] in
lemma presses (J : Knew G D p v x k s M r ε A) (hr : 0<r) (hP : ∀ᶠ y in 𝓝 x, (A y).IsHermitian) :
    ∀ᶠ y in 𝓝 x,(A y).PosDef := by
  filter_upwards [holds J.smooth.continuousAt J.gap (r/2) (half_lt_self hr) D p,hP] with y hy hh
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hh, fun f hf => ?_⟩
  simp only [star_trivial]; apply lt_of_lt_of_le _ (hy.lower f)
  refine mul_pos (half_pos hr) ?_
  have h : ∃ i, f i≠0 := by contrapose! hf; exact funext hf
  obtain ⟨i,hi⟩ := h
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi) (le_normSum f i)

omit [DecidableEq ι] in
lemma recovered (H : Bundle v G D p p A x k s M) : D.Schur p p s M (A x) := by
  have he := H.bound [] (by simp)
  rw [zeroth] at he; exact he.reclaim

lemma tag_poss {α β : ℝ} (hu : 1 ≤ U) (ha : 0 ≤ α) (hb : 0 ≤ β) (k : ℕ) : 0 ≤ tagPrice U k α β := by
  unfold tagPrice; have := lt_of_lt_of_le zero_lt_one hu; positivity

/-- Convenient common bundle for the letter producers. q will pay only
kernel excess per letter (need additional powers of 2,V,U for hit). -/
structure Speech (D : Cost X) (p : ι→X) (W : ι→Set ι) (G : Mark τ X) (v : τ→E) (A : E→Square ι) (x : E)
    (k : ℕ) (δ U C q ε : ℝ) : Prop where
  /-- no on-window hypothesis made for U as a function of y. -/
  dawn : ∀ i, i∈W i
  er : 0<δ
  letter : 1≤C
  profit : 0≤q
  coin : 0≤ε
  slip : ε ≤ 1
  paper : 1≤U
  motion : G.Move D δ U
  pd : ∀ᶠ y in 𝓝 x, Matrix.PosDef (A y)
  work : Bundle v G D p p A x k ((k+1:ℕ)*δ) C
  invert (u : ℝ) (hu : 0≤u) : Bundle v G D p p (action A u) x k ((k+1:ℕ)*δ) (C*attenuation u)
  glimpse (u : ℝ) (hu : 0≤u) (l : List τ) (hl : l.length ≤ k) :
    Mark.Bill G D p p l ((k+1:ℕ)*δ) (charges l.length ε C (drain u)) (jet v (fun y=>pie W (A y) u) l x)
  revise (u : ℝ) (hu : 0≤u) : Bundle v G D p p (fun y=>defect W (A y) u) x k ((k+1:ℕ)*δ) (q*attenuation u)
  arrange : Bundle v G D p p (fun y=>excess W (A y)) x k ((k+1:ℕ)*δ) q

namespace Speech
variable (J : Knew G D p v x k s M r ε A)

/-- Sum potential for all E or S overhead, uniform on radius. -/
def drawer (M r U V : ℝ) (k : ℕ) :=
    let C:=meter k k M U (rise V r); let J := tagPrice U k M (V*C)
    J+tagPrice U k M (tagPrice U k C J)
include J
lemma display (hs : ∀ᶠ y in 𝓝 x,(A y).IsHermitian) (hw : Price s M r d U V ε k)
    (hM : G.Move D (cash d k) U) (hb : D.Volume p d V)
    (hx : ∀ i,i∈W i) (hr : (study W hx).Near D p R)
    (hC : 1≤C) (hy : M ≤ C) (hV : V*meter k k M U (rise V r) ≤ C) (hd : meter k k M U (rise V r) ≤ C)
    (hq : Real.exp (-(k+1:ℕ)*d*R)*drawer M r U V k ≤ q) : Speech D p W G v A x k (cash d k) U C q ε := by
  set δ := cash d k with ht
  let L := meter k k M U (rise V r)
  let e := Real.exp (-(k+1:ℕ)*d*R)
  have he : 0 < e := Real.exp_pos _
  have hl := hw.pos
  have hc : 0<δ := cash_pos k hl
  have hm : Mark.Move G D d U := ⟨fun i x y => (hM.widen i x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (D.weight_mono (cash_bounds k hl).1 x y) (zero_le_one.trans hw.one)) (G.pos ..).le)⟩
  let t : ℝ := (k+1:ℕ)*δ
  have hf : t+k*δ ≤ d := (cash_bounds k hl).2
  have hk : t ≤ d := le_trans (le_add_of_nonneg_right (by positivity)) hf
  have hb' : t ≤ (k+1:ℕ)*d := le_trans hk (by push_cast; nlinarith only [hl, mul_nonneg hl.le (show 0≤(k:ℝ) by positivity)])
  have h4 : d ≤ 4*(k+1:ℕ)*d := by push_cast; nlinarith only [hl, mul_nonneg hl.le (show 0 ≤ (k:ℝ) by positivity)]
  let w := tagPrice U k M (V*L)
  let w' := tagPrice U k M (tagPrice U k L w)
  have hz : 0≤L := hw.meter_abs
  have h1 : 0 ≤ w := tag_poss hw.one hw.m (mul_nonneg hw.vol hz) k
  have h2 : 0 ≤ w' := tag_poss hw.one hw.m (tag_poss hw.one hz h1 k) k
  have hp : e*w ≤ q := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2) he.le).trans hq
  have hp' : e*w' ≤ q := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h1) he.le).trans hq
  have hh := presses J hw.r0 hs
  have hA : Bundle v G D p p A x k d M := (J.bundle hw.m hw.high).mono (h4.trans (hw.roomEnough.trans hw.roomTop)) le_rfl
  refine ⟨hx,hc,hC,(mul_nonneg he.le h1).trans hp,hw.low,hw.high,hw.one,hM,hh,hA.mono hk hy,
    fun u hu => (J.volume_price hw hu hm hb).mono (hk.trans h4) (mul_le_mul_of_nonneg_right hd (attenuation_pos hu).le),?_,?_,?_⟩
  · intro u hu l h
    have ht := glimpse_rates J hw (study W hx) hu hm hb l h
    rw [funext (f:=fun y => pie W (A y) u) (fun y => pie_inspects W _ _ hx)]
    apply ht.mono _ ((le_of_eq (show V*charges l.length ε L (drain u)=charges l.length ε (V*L) (drain u) from by unfold charges; split <;> ring)).trans
      (charges_mono _ hw.low hV (drain_pos hu).le))
    exact le_trans hb' (by push_cast; nlinarith only [hl,mul_nonneg hl.le (show 0≤(k:ℝ) by positivity)])
  · intro u hu
    rw [funext (f:=fun y => defect W (A y) u) (fun y => defect_survey W _ _ hx)]
    have hL := attenuation_pos hu
    exact (J.miss hw hu hm hb hr).mono hb' (le_trans (le_of_eq (show e*tagPrice U k M (V*(L*attenuation u))=e*w*attenuation u by unfold w tagPrice; ring))
      (mul_le_mul_of_nonneg_right hp hL.le))
  let D₀ := fun y => pie W (A y) 0-action A 0 y
  have hT : Bundle v G D p p D₀ x k d (tagPrice U k L (e*w)) := by
    have hh := J.discrepancy hw (u:=0) le_rfl hm hb hr
    unfold D₀; rw [show (fun y => pie W (A y) 0-action A 0 y)=TestD.glimpse (study W hx) A 0-action A 0 from
      funext fun y => congr_arg (·-action A 0 y) (pie_inspects W _ _ hx)]
    dsimp only at hh; simpa only [drain,add_zero, inv_one,mul_one] using hh
  let q₁ := tagPrice U k L (e*w)
  have hh : Bundle v G D p p (fun x => (1/2:ℝ) • (D₀ x + (D₀ x).transpose)) x k d q₁ :=
    (((hT.one_add hT.transpose).scale (1/2:ℝ))).mono le_rfl (by rw [abs_of_nonneg (by norm_num)]; unfold q₁; ring_nf; rfl)
  refine ((hA.multiply hh hM hc.le hw.one hw.m (tag_poss hw.one hz (mul_nonneg he.le h1) k) (show 0 ≤ t from by unfold t; positivity) hf).mono le_rfl
    (le_trans (le_of_eq (show tagPrice U k M q₁=e*w' from by unfold q₁ w' tagPrice; ring)) hp')).glue ?_
  filter_upwards [presses J hw.r0 hs] with y hy
  have hg : IsSymm ((A y)⁻¹) := Matrix.isHermitian_iff_isSymm.mp hy.inv.isHermitian
  change A y*((1/2:ℝ) • (D₀ y + (D₀ y).transpose))=A y*Next.SectorChange.Schur.clouded W (A y)-1
  unfold D₀ action resolve; rw [zero_smul,add_zero,← sym_change _ _ hg, ← sym_cloud,Matrix.mul_sub, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hy.det_pos.ne')]

omit J
variable (B : Speech D p W G v A x k δ U C q ε)
include B
lemma started (u : ℝ) (hu : 0≤u) : Bundle v G D p p (fun y=>pie W (A y) u) x k ((k+1:ℕ)*δ) (C*attenuation u) := by
  refine ⟨sculpted B.work.smooth B.pd.self_of_nhds B.dawn u hu,fun l hl=>?_⟩
  exact (B.glimpse u hu l hl).mono le_rfl (charges_lax _ B.slip (attenuation_pos hu).le (attenuation_le hu) (zero_le_one.trans B.letter))
lemma priced : Priced D p W (A x) ((k+1:ℕ)*δ) C q := by
  refine ⟨B.dawn, B.pd.self_of_nhds,B.letter,mul_nonneg (by positivity) B.er.le,B.profit,recovered B.work,
      fun u hu => recovered (A:=action A u) (B.invert u hu),fun u hu => recovered (A:=fun y=> pie W (A y) u) (B.started u hu),fun u hu => recovered (A:=fun y=>defect W (A y) u) (B.revise u hu), recovered (A:=fun y=>excess W (A y)) B.arrange⟩
end Speech
end YM.AnalyticBridge.RelativeLogdet.Differential
