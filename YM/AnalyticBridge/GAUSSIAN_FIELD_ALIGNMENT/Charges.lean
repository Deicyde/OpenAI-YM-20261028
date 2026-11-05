import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Completed
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Operators
import YM.Push.FREE_RESOLVENT.AffineResolvent
import YM.Push.FREE_RESOLVENT.Tags


set_option warningAsError false

/-!
# One fixed-L purchase on the actual (tree, sector, horizon) counting matrices

The active-part free comparator compresses the same flat path Gram (or
Hessian, when attached and uncut) *before* pricing principal matrices. Also
supply the direct full-key comparison, via identity completion of the actual
precision to `raw` and the separate no-hole `Affine.whole`. In neither case
identifying a nonsymmetric ordered-window inverse with a covariance, nor
equating the cutoff precision to a principal submatrix of an uncut Gaussian
covariance. Pay for global changes where needed. The uniformity here costs
only after L; and in the unequal-kernel case a bound not small is not an
affordability claim. At flat background the cut-vs-uncut difference in the
same active space DOES pay exponentially in the true path cut degree.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment
open Function Set Filter Lattice Wilson RG Precision Exterior Tree Matrix
open Next.SectorChange Next.SectorChange.Rows Pressure Pressure.Stores Schur Wisps Relative Bid
open FreeResolvent.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (A : Stores S) (F : Forest S.ratio) (x : ℝ) (T : Tube G S)
  (k : S.Choices)

lemma endsAt_bars (h : 120 ≤ radiusB x) : Bars (endsAt (G:=G) S x) (home S) (radiusB x / 60) := by
  intro i j H y hy z hz
  have hi : separation y (home S i) ≤ 1 := (separation_comm ..).trans_le (meetings (FreeResolvent.Mid.cull i) (S:=S) hy)
  have hj : separation (home S j) z ≤ 1 := meetings (FreeResolvent.Mid.cull j) (S:=S) hz
  have he := separation_triangle y (home S i) (home S j)
  have ht := separation_triangle y (home S j) z
  omega

lemma midsAt_bars (h : 200 ≤ radiusB x) : Bars (midsAt (G:=G) S x) (home S) (radiusB x / 60) := by
  intro i j he
  by_contra H
  have h' : j ∉ range ((FreeResolvent.Mid.cutView G S (radiusB x)).loc i) := by rintro ⟨⟨j,hj⟩,rfl⟩; exact H hj
  have ht := FreeResolvent.Mid.near G S (radiusB x) h _ _ h'
  let q := separation (home S i) (home S j)
  have hi : ((q:ℝ) * 60) ≤ radiusB x := by exact_mod_cast Nat.mul_le_of_le_div 60 _ _ he
  have hx : (200:ℝ) ≤ radiusB x := by exact_mod_cast h
  change _ ≤ (q:ℝ) at ht
  linarith



def freePart (r : Admit) :=
    (primary S F k T.high T.up r 0).submatrix (live A F x) (live A F x)

lemma block_symm (r : Admit) (B : Gaussian.Vec (Raw G c)) : (block S k T.high T.up r B).IsSymm := by
  unfold Matrix.IsSymm block channel squareQ
  simp only [transpose_smul,transpose_sum, transpose_add, transpose_mul,transpose_transpose]

structure MatrixBounds {α : Type} [Fintype α] (p : α → Site c) (s η M : ℝ) (Q : Gaussian.Table α) : Prop where
  pours : Pours Q p p s M
  symm : Q.IsSymm
  lower : Gapped Q η

section abstract
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {s M η : ℝ}

omit [DecidableEq α] [DecidableEq β] in
lemma MatrixBounds.compress {e : α ↪ β} {p : β → Site c} {Q : Gaussian.Table β} (h : MatrixBounds p s η M Q) :
    MatrixBounds (p ∘ e) s η M (Q.submatrix e e) :=
  ⟨to_pours ((of_pours h.pours).submatrix e.injective e.injective) h.pours.pos,
    h.symm.submatrix e,gap_iff.mpr ((gap_iff.mp h.lower).submatrix e e.injective)⟩

lemma MatrixBounds.pad {e : α ↪ β} {p : β → Site c} {Q : Gaussian.Table α} (h : MatrixBounds (p ∘ e) s η M Q) :
    MatrixBounds p s (min η 1) (M+1) (fill e Q) :=
  ⟨Completed.pours p e h.pours,Completed.sym e h.symm,Completed.gapped e h.lower h.symm⟩

omit [DecidableEq α] in
lemma MatrixBounds.mono {p : α → Site c} {Q : Gaussian.Table α} (h : MatrixBounds p s η M Q) {s' η' M' : ℝ}
    (hs : s' ≤ s) (he : η' ≤ η) (hm : M ≤ M') : MatrixBounds p s' η' M' Q :=
  ⟨h.pours.weaker hs hm,h.symm,gap_iff.mpr ((gap_iff.mp h.lower).mono he)⟩
end abstract

section free
variable {P : Teller G} (ht : P.Funds S T) (hL : Larger (G:=G) S)

def fineCap (G : Gauge) (P : Teller G) (d : Patch) := stageCost G d P.bind P.top.clip 0 P.top.paths P.top.width

def tailCap (G : Gauge) (P : Teller G) (d : Patch) := 2*(FreeResolvent.tagPrice 1 0 (phasePrice G d P.bind 0 P.top.paths P.top.width) (phasePrice G d P.bind 0 P.top.paths P.top.width))
lemma tailCap_nn (G : Gauge) (P : Teller G) (d : Patch) : 0 ≤ tailCap G P d := by
  have h := phase_nn G d P.bind (k:=0) P.top.width_pos P.top.paths_pos.le
  unfold tailCap FreeResolvent.tagPrice; positivity

include ht hL
lemma free_sound (r : Admit) : MatrixBounds (FreeResolvent.theta S.ratio F) (tier P.top.width 0)
    (headGap G S.patch P.bind P.top.clip) (fineCap G P S.patch) (primary S F k T.high T.up r 0) := by
  have hu := stage_nn G S.patch P.bind P.top.clip (k:=0) P.top.width_pos P.top.paths_pos.le
  obtain ⟨l,m,H,H'⟩ := ht.feeds
  rw [← ht.high] at H
  have hp := knows F k P.top.width_pos P.top.paths_pos.le (path_sheet T H) hL T.high 0 r
  unfold fineCap; rw [← ht.knobs,← ht.high] at *
  exact ⟨to_pours hp.schur hu,(block_symm T k r 0).submatrix _,gap_iff.mpr hp.gap⟩

lemma free_tail (n : ℕ) :
    let U := primary S F k T.high T.up
    Pours (U (shorter n) 0 - U all 0) (FreeResolvent.theta S.ratio F) (FreeResolvent.theta S.ratio F) (tier P.top.width 0)
      (Real.exp (-(P.top.width/4)*n)*tailCap G P S.patch) := by
  obtain ⟨l,m,H,H'⟩ := ht.feeds
  rw [← ht.high] at H
  have he := tail_primary S (k:=0) hL.2.2 P.top.width_pos P.top.paths_pos.le (path_sheet T H) (le_refl (0:ℝ))
    (ordering P.top.width_pos 0).1.le n F T.high k
  have hh := he.bound [] le_rfl |>.reclaim.neg
  intro U
  rw [FreeResolvent.TestD.zeroth, Pi.sub_apply, neg_sub] at hh
  have hv := tailCap_nn G P S.patch; unfold tailCap at *; rw [← ht.knobs] at *
  exact to_pours hh (mul_nonneg (Real.exp_pos _).le hv)

lemma flat_exact (V : Config G c) (hv : V=1) : Rows.gram T x V k (shots S x) A F = freePart A F x T k (shorter (till x)) := by
  obtain ⟨l,m,H,H'⟩ := ht.feeds
  rw [← ht.high] at H
  have he := (affine_near A F x T k hL.1 H).self_of_nhds
  simpa only [show (decode (0 : Gaussian.Vec (Raw G c))) = 0 from rfl, Precision.link_one, hv, freePart] using he
end free

/-- `Supported` of the two sector prescriptions, and other comparators
actually priced at unmasked `hessian`/retained `Bed` (identification under
usual path/algebra checks, see `unmasked`). `whole` uses ALL non-tree
variables. To compare to that law we work on `Raw`, with identity padding
on the truly selected A's inactive complement. -/
structure Ready (V : Config G c) (s η M D : ℝ) : Prop where
  side : 200 ≤ radiusB x
  solvent : Gapped (Rows.gram T x V k (shots S x) A F) η
  ends : Supported (Rows.gram T x V k (shots S x) A F) (panels A F) (front A F) ((radiusB x/60:ℕ):ℝ) s M
  mids : Supported (Rows.gram T x V k (shots S x) A F) (mids A F x) (front A F) ((radiusB x/60:ℕ):ℝ) s M
  free (r : Admit) : Supported (freePart A F x T k r) (GaussianFieldAlignment.mids A F x) (front A F) ((radiusB x/60:ℕ):ℝ) s M
  wide : Supported (fill (address A F x) (Rows.gram T x V k (shots S x) A F)) (endsAt S x) (home S) ((radiusB x/60:ℕ):ℝ) s M
  whole (r : Admit) : Supported (whole S F k T.high T.up r 0) (midsAt S x) (home S) ((radiusB x/60:ℕ):ℝ) s M
  level : V=1 → Pours (Rows.gram T x V k (shots S x) A F - freePart A F x T k all) (front A F) (front A F) s (Real.exp (-s*till x)*D)

lemma whole_pad (r : Admit) : whole S F k T.high T.up r 0 = fill (freeTo G S F) (primary S F k T.high T.up r 0) :=
    Eq.symm (fill_pad (freeTo G S F) _)

/-- Constants depend only on Teller & patch, AFTER L (not p, fields or
volume, nor the number of uses within this smoothing-index pair). No need
for Directed or another choice of data to establish this jointly with the
retained horizon estimates. True charge proof on correct flag cells; special
`V=1` alternative works on arbitrary active placements. -/
theorem purchase (P : Teller G) (d : Patch) (hd : d.Branches P.bind G) :
    ∃ s η M D : ℝ, 0<s ∧ 0<η ∧ 0<M ∧ 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=d → Larger (G:=G) S → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags = RG.flags (temp x) V ∨ V=1 → Ready A F x T k V s η M D := by
  obtain ⟨v,K,η,_,_,hv,hK,hη,_,_,H1⟩ := opaqueCost G d P hd
  let w := P.top.width; let t := tier w 0
  let γ := min η (headGap G d P.bind P.top.clip)
  let E := min γ 1
  have hw := P.top.width_pos
  have hy : 0<t := (ordering hw 0).1
  have he : 0<E := lt_min (lt_min hη (headGap_pos ..)) zero_lt_one
  let b := fineCap G P d; let a := max b K
  have ha : 0 ≤ a := le_trans hK (le_max_right ..)
  let B (s : ℝ) := max 0 (FreeResolvent.torusPay (Bloch.Co d.L (FreeResolvent.PAC G 1)) s)
  obtain ⟨s,M,hs,hv',hp,H⟩ := same_purchase (lt_min hv hy) (M:=a+1) (by positivity) he B (fun _ => le_max_left ..)
  have hr : Tendsto (fun x => radiusB x/60) atTop atTop := by
    refine tendsto_atTop.mpr fun i => ?_
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x h; omega
  have hv'' : t ≤ P.top.width/4 := by unfold t tier w; norm_num; linarith
  have hb : b ≤ a := le_max_left ..; have hK' : K ≤ a := le_max_right ..
  refine ⟨s,E,M,tailCap G P d,hs,he,hp,tailCap_nn ..,?_⟩
  filter_upwards [H1,hr.eventually H, Work.E01.radiusB_tendsto.eventually_ge_atTop 200] with x h1 hx h2
  intro c f S T hS hL hl hT A F k V hA
  let e := address A F x (G:=G); let p' := home (G:=G) (r:=1) S; let p := front (x:=x) A F (G:=G)
  have hB0 z (hz : 0 < z) : (FreeResolvent.native c).Volume p' z (B z) := (home_volume S 1 z hz).le (by unfold B; rw [hS]; exact le_max_right ..)
  have hB : Revenue p' B := fun z hz => (hB0 _ hz).bound
  have hB' : Revenue p B := fun z hz => ((hB0 _ hz).comp e.injective).bound
  let Q := Rows.gram T x V k (shots S x) A F
  let R (r) := primary S F k T.high T.up r 0
  have ht (r) : MatrixBounds (FreeResolvent.theta S.ratio F) (min v t) γ a (R r) := by
    have h := free_sound F T k hT hL r; rw [hS] at h; exact h.mono (min_le_right ..) (min_le_right ..) hb
  have hu (r) : MatrixBounds p (min v t) γ a (freePart A F x T k r) := (ht r).compress (e:=live A F x)
  have hq : MatrixBounds p (min v t) γ a Q := by
    rcases hA with hA|hA
    · obtain ⟨ht,hq,-,-,-⟩ := h1 S T hS hl hT A F k V hA
      exact (MatrixBounds.mk ht (sym_gram ..) hq).mono (min_le_left ..) (min_le_left ..) hK'
    unfold Q; rw [flat_exact _ _ _ _ _ hT hL V hA]; exact hu _
  have hz := hq.mono le_rfl (show E ≤ γ from min_le_left ..) (le_add_of_nonneg_right (b:=1) zero_le_one)
  have H2 := hx Q p (mids A F x) hB' hz.pours hz.symm hz.lower (mids_bars A F x (by omega))
  have H3 := hx Q p (panels A F) hB' hz.pours hz.symm hz.lower (boards A F G (by omega))
  have H4 := hx (fill e Q) p' (endsAt S x) hB (hq.pad (e:=e) (p:=p')).pours (hq.pad (e:=e) (p:=p')).symm (hq.pad (e:=e) (p:=p')).lower (endsAt_bars x (by omega))
  refine ⟨h2,hz.lower,H3,H2,fun r => ?_,H4,fun r => ?_,fun h => ?_⟩
  · have h := (hu r).mono le_rfl (show E ≤ γ from min_le_left ..) (le_add_of_nonneg_right (b:=1) zero_le_one)
    exact hx _ p (mids A F x) hB' h.pours h.symm h.lower (mids_bars A F x (by omega))
  · rw [whole_pad]
    have h := (ht r).pad (e:=freeTo G S F) (p:=p')
    exact hx _ p' _ hB h.pours h.symm h.lower (midsAt_bars x h2)
  rw [flat_exact _ _ _ _ _ hT hL V h]
  have hh := of_pours (free_tail F T k hT hL (till x)) |>.submatrix (live A F x (G:=G)).injective (live A F x).injective
  rw [hS] at hh
  have H : s ≤ t := hv'.trans (min_le_right ..)
  have hD := tailCap_nn G P d
  exact to_pours (hh.mono H (show Real.exp (-(P.top.width/4)*(till x)) * tailCap G P d ≤ _ from
    mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))) hD)) (by positivity)

section use
variable {A F x T k} {V : Config G c} {s η M D : ℝ} (h : Ready A F x T k V s η M D)

include h
lemma Ready.exchange (hs : 0 ≤ s) :
    let Q := Rows.gram T x V k (shots S x) A F
    Difference (per (panels A F) Q) (per (GaussianFieldAlignment.mids A F x) Q) (front A F) s (error M s (↑(radiusB x / 60)) 0) := by
  exact Relative.compare h.ends h.mids (to_pours (by rw [sub_self]; exact FreeResolvent.Cost.Schur.zero le_rfl) le_rfl) hs

lemma Ready.change (hs : 0 ≤ s) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : Prices G (Next.SectorChange.Active A x F)) (f : Prices G (Next.SectorChange.Active A x F) → X) :
    let C := fog A F T x V k; let H := middle A F x T V k
    (MeasureTheory.Integrable f (Gaussian.cloud C) ↔ MeasureTheory.Integrable (fun z => trade C H u z • f (u+z)) (Gaussian.cloud H)) ∧
      (∫ z, f z ∂Gaussian.cloud C) = ∫ z, trade C H u z • f (u+z) ∂Gaussian.cloud H :=
  (h.exchange hs).change u f






end use
end YM.AnalyticBridge.GaussianFieldAlignment
