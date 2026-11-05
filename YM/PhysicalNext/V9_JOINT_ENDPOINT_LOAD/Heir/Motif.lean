import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Safeguard
import YM.Next.MULTISOURCE.Lanes
import YM.Next.WARD_BIN.Wallet
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Border
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Morceau
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Ray


/-! # Ordered sharp E fee, before the moving-density scores

One common protected fine-gauge model log for the entire test even
on the stochastic ray; PMOM-style attenuation modified to only two
input grades. Works at fixed centered Z of the original coordinates
on this torus, and unattached to independent resamplings of centered
marginals or recomputed likelihoods from training gauges. Actual
`Y` & `X` must fit here according to the E contour declaration. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo WardBin.Lies Planned.AtomRegular
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {o : Site f} {g : Site c → G.El} {X : Support f} {Y : Support c} {Q C M r t x τ : ℝ} {I : Type}
    {A : Stores S} {n l : ℕ} {D : Slab G c l} {q : Chi} {d u : ℝ} {f' : Config G f → ℝ}

def radial (G : Gauge) := (Flair.strings G).choose
lemma radial_pos (G : Gauge) : 0<radial G := (Flair.strings G).choose_spec.1
structure Weft (G : Gauge) (L : Side) (P B : BudgetPoint) (Q C x : ℝ) : Prop where
  squared : radial G*(Q*loom P (reach x) C)^2 ≤ B.threshold
  width : B.threshold*(1+6*(1+(radiusB x : ℝ))*L.val)^B.power ≤ 1
  cover : B.B ≤ 2*radiusB x

section holds
variable (a : Museum F x A X Y I) [Fintype I] (b : Folio.Bulletin x Pt T) (hr : Weft G S.patch.L P B Q C x) (hT : Act T F x k n r Q) (hs : Short S B X)
    (hq : Canvas P (S.ratio.parent o) (reach x) V g n C) (ho : o∈X) (hC : 1≤C) (hM : loom P (reach x) C < r) (U : Config G f) (w : Prices G I)
    (hw : ‖a.extra g u w‖ ≤ loom P (reach x) C)
include b hr hT hs hq ho hC hM hw

omit b hr hT hs hq ho hC hM hw [Fintype I] in
lemma flowJourney (V : Config G c) (D : Slab G c l) : Tendsto (journey V _ D) (𝓝 0) (𝓝 V) := by
  obtain ⟨Y,hY,h,H⟩ := journey_lift V l D
  apply Tendsto.congr' H.symm; exact (show Tendsto (increment V) (𝓝 (0:Directions G c)) (𝓝 V) from by
    simpa only [Work.G07.at_zero_increment] using!
      (show Continuous (increment V) by unfold increment; fun_prop).tendsto (0:Directions G c)).comp (hY ▸ h.continuousAt.tendsto)

lemma depicted (D : Slab G c l) : let v := enters V (S.ratio.parent o) (reach x) g D (a.extra g u w); let Z := journey V l D
    ∀ᶠ y in 𝓝 (0:Panels l), Agrees (inspected X) (increment 1 (display T F x k true (v y))) (gauge (fun j => G.lieExp (φ T F true (v y).1 j))
      (gauge (g ∘ S.ratio.parent) (a.received k T q d u (Z y) U w))) := by
  intro v Z
  have he : ‖v 0‖ ≤ loom P (reach x) C := max_le ((congrArg (‖·‖) (launch_zero D)).trans_le (hq.paid hC)) hw
  have ht := ((show ContinuousAt v 0 from (readyEnter hq).continuousAt).norm.eventually (gt_mem_nhds (he.trans_lt hM)))
  filter_upwards [ht,(flowJourney V D).eventually hq.seen] with y hy hz
  rw [hT.represents true _ hy.le]; intro i hi hj
  exact a.heard g u b hi hj (a.asks_origin ho) ((separation_comm ..).le.trans ((short_patch hs hr.cover ho hi).trans (by omega))) true w U hz

-- Conditions valid unmasked at evaluation and radial interpolation. Inequality
-- slack from `strict` at endpoint is not required in this attenuation.
lemma plucked (D : Slab G c l) (hQ : 1≤Q) (hn : 1≤n) (hN : Q*loom P (reach x) C ≤ 1) (hB : Healthy B.threshold X (a.received k T q d u V U w)) :
    let v := enters V (S.ratio.parent o) (reach x) g D (a.extra g u w)
    let z := display T F x k true (v 0)
    (∀ e, Mom.needed X e → ‖z e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1) ∧ ∀ s∈Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (s • z)) := by
  intro v z; have he : ‖v 0‖ ≤ loom P (reach x) C := max_le ((congrArg (‖·‖) (launch_zero D)).trans_le (hq.paid hC)) hw
  have hh := display_price hT hn he hM.le hQ
  have hz : Healthy B.threshold X (increment 1 z) := by
    have ht := (depicted (q:=q) (d:=d) a b hr hT hs hq ho hC hM U w hw D).self_of_nhds
    have he := flags_agree B.threshold _ _ X ht
    rw [gauge_flags,gauge_flags,Sample.journey_origin V D] at he
    change Disjoint _ _ at hB ⊢; rwa [Finset.disjoint_iff_inter_eq_empty,he,←Finset.disjoint_iff_inter_eq_empty]
  refine ⟨fun e he' => ⟨(norm_le_pi_norm z _).trans (hh.trans hN),?_⟩, (Flair.strings G).choose_spec.2 _ X _ _ z hN ((norm_nonneg _).trans hh) hr.squared
    (fun i _ => (norm_le_pi_norm z _).trans hh) hz⟩
  apply le_trans _ hr.width; have hh := B.threshold_pos; unfold Lyre.width; gcongr
  exact_mod_cast (close_enough (B:=B) ho (Finset.mem_union_left _ he'.1)).trans (width_le hs hr.cover)
end holds

variable (Q' : Rights G n) (hG : G.Simple) (a : Museum F x A X Y I) [Fintype I] (b : Folio.Bulletin x Pt T) (hr : Weft G S.patch.L P B Q C x)
    (hT : Act T F x k n r Q) (hq : Canvas P (S.ratio.parent o) (reach x) V g n C) (hC : 1 ≤ C) (hh : Matins T F B.power (2*C) M)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hk : 5 ≤ n) (hK : n ≤ B.order) (hF : 100*(1+radiusB x) ≤ c.val)
    (hP : P.threshold=temp x) (ht : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (h' : loom P (reach x) C < r) (hy : Q*loom P (reach x) C ≤ 1)
    (hS : Short S B X) (he : Seed B o X f') (hE : B.supBounds o X f' τ)
    (h : ∀ i, P.dirBound (S.ratio.parent o) (D i)) (hl : l ≤ n)
    (U : Config G f) (w : Prices G I) (hU : Healthy B.threshold X (a.received k T q d u V U w))
    (hu : 0 ≤ u) (hw : u*‖tape w‖ ≤ loom P (reach x) C)

def shortFee (Q' : Rights G n) := patterns n * ((n+1:ℝ)*3^n*Q'.fee)
include hG b hr hT hq hC hh hQ hM hk hK hF hP ht hpow h' hy hS he hE h hl hu hw hU

lemma motif : let f₀ (V : Config G c) := f' (a.received k T q d u V U w)
    let K := M+tranche S.patch.L n Q (loom P (reach x) C) (u*‖tape w‖) B.threshold
    ContDiffAt ℝ n (f₀ ∘ journey V l D) 0 ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (f₀ ∘ journey V l D) 0‖ ≤ shortFee Q' * K^n * ((S.patch.L.val:ℝ)⁻¹)^5 * τ := by
  intro f₀ K
  have hw' := (a.extra_size g u hu w).trans hw
  have hK' : 1 ≤ K := le_trans hM (le_add_of_nonneg_right (tranche_nn _ _ (by positivity) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le))
  let L := enters V (S.ratio.parent o) (reach x) g D (a.extra g u w)
  let z := display T F x k true ∘ L; let fSide := f; let f := f' ∘ increment (1:Config G _)
  obtain ⟨he',hz⟩ := plucked a b hr hT hS hq he.site hC h' U w hw' D hQ (by omega) hy hU
  have hf : ContDiffAt ℝ n f (z 0) := (along he.good (by simpa only [one_smul,z,Function.comp_apply,L] using hz 1 (by simp))).of_le (Nat.cast_le.mpr hK)
  have hs := (depicted (q:=q) (d:=d) a b hr hT hS hq he.site hC h' U w hw' D)
  have hs : f ∘ z =ᶠ[𝓝 0] f₀ ∘ journey V l D := by
    filter_upwards [hs] with i hi; exact (he.good.sites _ _ (agrees_mono hi (fun _ hv => Finset.mem_union_left _ hv))).trans ((he.good.symmetry _ _).trans (he.good.symmetry ..))
  have hE' : loom P (reach x) C ≤ 1 := le_trans (le_mul_of_one_le_left ((mul_nonneg hu (norm_nonneg _)).trans hw) hQ) hy
  have hg := (timesEnter hq hT hP (by omega) h hC hl hQ hE' h'.le hw' true).1
  have h (j) (hj : j ≤ n) := first_promise (X:=X) hh hq ht hP hpow hC hl h hE' hT hQ hM (by omega) h'.le hw' (a.extra_size g u hu w) hj
  refine ⟨(hf.comp (f:=z) _ hg).congr_of_eventuallyEq hs.symm,fun j hj => ?_⟩
  have h0 : Promise 2 K ((S.patch.L.val:ℝ)⁻¹) B o X (z 0) := by
    simpa only [iteratedFDeriv_zero_apply] using h 0 (Nat.zero_le _) 0 (by simp)
  have hn : 4 ≤ fSide.val := S.sizes ▸ Nat.le_trans (show 4 ≤ c.val by omega) (Nat.le_mul_of_pos_right _ S.patch.L.property)
  rw [← (hs.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]; have hlarge := Q'.large; have hτ := hE.1
  refine (slots_bound (U:=z) hg hf hj (C:=(n+1:ℝ)*((3*K)^n*((S.patch.L.val:ℝ)⁻¹)^5)*Q'.fee*τ) (by positivity) (fun p v hv => ray hG he (short_nonwrap hS hr.cover hF he.site) hn hE (by positivity)
    (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr S.patch.L.property)) hK' Q' hK _ h0 he' hz hk (p.length_le.trans hj) _ (fun i => h _ ((p.partSize_le i).trans hj) _ (fun k => hv _)))).trans_eq ?_
  unfold shortFee; rw [mul_pow (3:ℝ)]; ring
end YM.PhysicalNext.JointLoad.Heir
