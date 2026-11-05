import YM.TraceExtension.Anchor.Small
import YM.TraceExtension.Anchor.Table

/-! late IR equality; accommodates a linear combination of moving columns and root probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Function Filter Set MeasureTheory Analysis Extraction Around Table Ward Cells Lattice Wilson Next.UVStress MergeProof MergeProof.Accent
  Bid MergeProof.Ribbons
open Asymptotics
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S : Table C.book} {d D : ℕ}

abbrev CutNet (C:Family G) := ∀ _k : ℕ, ∀ N p, Config G (C.side N p) → ℂ
def smoke (I:Watch C)(x:Cover)(F:CutNet C)(k N p:ℕ):=
    moment (C.beta N p) (fun U=> F k N p U * I.plot N p (Lattice.translate (- Cells.location C.S k N p x) U))

/-- Mixed cluster equality with field evaluated in displaced Watch geometry. The filter on the right is the same for all k. -/
def Book (b:Filter (ℕ×ℕ))(F:CutNet C)(v:ℕ→S.Field d):Prop:=
   ∀ I: Watch C, ∃ c:ℝ, 0<c ∧ ∃ E:ℕ→ℝ, Fast C.S E ∧ ∀ᶠ k:ℕ in atTop, ∀ (l:ℤ)(a:Axis), |(l:ℝ)*C.S.a k| ≤ c →
      ∀ᶠ i: ℕ×ℕ in b, ‖smoke I (l • step a) F k i.1 i.2-plant I S d (((l:ℝ)*C.S.a k) • basis a) (v k)‖ ≤ ‖E k‖

lemma grid_step (C:Family G)(k:ℕ)(l:ℤ)(a:Axis): C.S.gridPoint k (l • step a)= (((l:ℝ)*C.S.a k) • basis a):= by
   ext1 i; by_cases h:i=a <;> simp [*,Schedule.gridPoint,mul_comm]
lemma screen (I:Watch C) : ∃ c:ℝ,0<c∧ ∀ x : E4, ‖x‖ ≤ c→ rows I x ∈ generic _:= by
   have h : ∀ᶠ x:E4 in nhds 0, rows I x ∈ generic _:= by
      have hu : rows I 0 ∈ generic _ := by rw [at_home]; exact I.wild
      have hv : Continuous (rows I) := Work.A02.continuous_cons.comp (continuous_id.prodMk continuous_const)
      exact hv.continuousAt ((genericOpen _).mem_nhds hu)
   obtain ⟨ε,H,hK⟩:= Metric.mem_nhds_iff.mp h; exact ⟨ε/2,half_pos H,fun x hx=>hK (by simpa using (hx.trans_lt (half_lt_self H)))⟩

/-- Coarse observable pullback produces late physical equivalence for a given anchor funding certificate. -/
lemma from_center (H:C.Makes) (h : CellHyp C F) (he:F.PointLimits C S) (hs:S.Hierarchy)
    {X : CutNet C} {b : Filter (ℕ×ℕ)} [b.NeBot](hb:b ≤ F.fuse) {v : ℕ→ℕ×ℕ→ C.label D} {u : ℕ → C.label D}
    (hx : ∀ᶠ k:ℕ in atTop, Tendsto (v k) b (𝓝 (u k)))
    (hP : ∀ J:ℕ, ∃ E:ℕ→ℝ,Fast C.S E∧∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ×ℕ in b,∃ hN:J ≤ i.1,
       let T:= center C.S i.2 hN 0
       let q:= X k i.1 i.2- C.O i.1 i.2 (v k i) 0
       Interior (T.chamber 0) q ∧ T.rootTest (C.beta i.1 i.2) q ≤ E k):Book b X (fun k=>S.project D (u k)):=by
    intro I
    obtain ⟨B,hB,hq⟩:=sails I H h I.t le_rfl
    obtain ⟨E,HQ,HP⟩:= hP I.t
    obtain ⟨c,hc,hδ⟩:= screen I
    let r:=min c (C.S.a I.t / 8); have hR:0<r:= lt_min hc (div_pos (C.S.a_pos _) (by norm_num))
    let e:= fun i=> E i * B + factor C.S (-1) i; have hZ:Fast C.S (factor C.S (-1)):=⟨-1,by norm_num,isBigO_refl ..⟩
    refine ⟨r,hR,e, Fast.add (HQ.mul (fun p hp=> factor_const C.S B p hp)) hZ,?_⟩
    filter_upwards [hx,HP] with k hK hp
    intro l a ha
    let z:Cover:= l • step a; let x:= C.S.gridPoint k z
    have hX : x= ((l:ℝ)*C.S.a k) • basis a:=grid_step C k l a
    have ht:= hδ x (show ‖x‖≤ c from by rw [hX]; simpa [norm_smul] using ha.trans (min_le_left ..))
    let P:= plant I S D x (S.project D (u k)); let D' (i:ℕ×ℕ):=C.numeric i.1 i.2 (Fin.cons (α:=fun _=> C.book.Token) ⟨D,v k i⟩ I.q) (Fin.cons (α:=fun _=>Site (C.side i.1 i.2)) (Cells.location C.S k i.1 i.2 z) (I.among i.1 i.2))
    have hu : Tendsto D' b (𝓝 P):=by
       have hz:= evaluates I he hb k z ht hK
       rw [← S.at_project S hs.laws.toSymmetric (fun _=>le_rfl) (generic_conf _ ht) (Fin.cons (α:=fun _=>C.book.Token) ⟨D,u k⟩ I.q),Work.A01.comp_cons] at hz; unfold P plant; rw [Work.A01.front_eval]; exact hz
    rw [← hX]
    filter_upwards [hp,hq.filter_mono hb,(large_mesh F k).filter_mono hb, Metric.tendsto_nhds.mp hu (factor C.S (-1) k) (Real.exp_pos _)] with i hi hq hI H'
    let u':= (Cells.location C.S k i.1 i.2 z); let f:Config G (C.side i.1 i.2)→ℂ:=fun x=> I.plot i.1 i.2 (Lattice.translate (-u') x)
    obtain ⟨hN,h,h'⟩:=hi; let Q:= center C.S i.2 hN 0; let C₁:= X k i.1 i.2; let C₂:= C.O i.1 i.2 (v k i) 0; let β:=C.beta i.1 i.2; let μ:=law G (C.side i.1 i.2) β
    change ‖smoke _ _ _ _ _ _-P‖≤_
    have hf : Continuous f:=by unfold f Watch.plot; apply continuous_finsetProd; intro j _; exact (C.continuousO ..).comp (show Continuous (Lattice.translate (-u') : Config G _→ Config G _) from by unfold Lattice.translate; fun_prop)
    have hl C' (H:Integrable C' μ) : Integrable (fun U=>C' U*f U) μ:= by
       simp_rw [mul_comm _ (f _)]
       exact Next.UVStress.final_mul _ _ _ (RG.Envelope.compactC hf) H
    have hc' : Integrable (C₁-C₂) μ:= by obtain ⟨G,hG⟩:= h.cost; exact Integrable.of_bound h.borel.aestronglyMeasurable G (Eventually.of_forall hG)
    have hh : Integrable C₂ μ:= (C.continuousO ..).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hy : Integrable C₁ μ:= (show C₁-C₂+C₂=C₁ from sub_add_cancel ..) ▸ hc'.add hh
    have ha: ‖smoke I z X k i.1 i.2 - D' i‖ ≤ E k *B := by
       have hx := ((hq.choose_spec _ h _ hI l a (ha.trans (min_le_right ..))).trans (mul_le_mul_of_nonneg_right h' hB))
       rw [show D' i=_ from pitches I z ⟨D,v k i⟩]
       unfold smoke moment
       change ‖(∫ V,C₁ V*f V∂μ)-(∫ V,C₂ V*f V∂μ)‖≤ _
       rw [← integral_sub (hl _ hy) (hl _ hh)]
       simp_rw [← sub_mul]; exact hx
    have hζ:= (norm_sub_le_norm_sub_add_norm_sub (smoke I z X k i.1 i.2) (D' i) P).trans (add_le_add ha ((dist_eq_norm (D' i) P) ▸ H'.le))
    exact hζ.trans (Real.le_norm_self _)
end YM.Trace.Pull
