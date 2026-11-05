import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alabaster
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Sector
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Chains
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Marginals



/-! Slices fit the actual Desk. All addresses, ordered chains and
zero-overlap support rule. We pad to ℕ in the API; the dictionary in
assembly retains the finer countable types. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Notify
open Function Filter Set Matrix MeasureTheory Lattice RG Wilson Pressure Tree
open Next.SectorChange Gaussian Schur FreeResolvent Precision
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian
open AnalyticBridge.Annulus.Map
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Completion

/-! Numberings injective even on locations at which values happen to
agree. No aggregation by sum across addressed chains, except for pairing
absolute Fsct vs Aflat at the *same* chain, and combining on colors inside
each. -/
section numbers
variable (J : Type*) [Countable J]
def barcode : J ↪ ℕ :=
  ⟨(exists_injective_nat J).choose, (exists_injective_nat J).choose_spec⟩
variable {J}
def number (F : J → ℝ) : ℕ→ℝ := Function.extend (barcode J) F 0
lemma charged (F : J→ℝ) (i : J) : number F (barcode J i)=F i := (barcode J).injective.extend_apply _ _ _
lemma unused (F : J → ℝ) (i : ℕ) (h : i ∉ Set.range (barcode J)) : number F i=0 :=
  Function.extend_apply' _ _ _ h
lemma numbered {F : J → ℝ} {x} (h : HasSum F x) : HasSum (number F) x := (hasSum_extend_zero (barcode J).injective).2 h
end numbers

section service
open Wires
variable {G : Gauge} {c f : Side} {S : StepData c f}
  (d : AnalyticBridge.LocalGaussian.Desk G S) (F : Forest S.ratio) (k₀ : S.Choices)

structure Lit (d : AnalyticBridge.LocalGaussian.Desk G S) : Prop extends Route.Badge.App d where
  reception : ∃ v C η b r : ℝ,
    Physical.Certified S d.tube d.betaHat v C η b ∧
    Physical.parcel G S 20 0 v C b r (radiusB d.betaHat) 0 ∧
    Physical.parcel G S 20 0 v C b r (radiusB d.betaHat) 1

abbrev chosen (A : Stores S) (k : S.Choices) : Spot d := Route.Badge.camera d F (Native.kinetic d.tube F k₀ d.betaHat) A k

abbrev Dots (f : Side) := Bond f ⊕ Letter (Bond f) 1

variable (A : Stores S) (k : S.Choices) (V : Config G c)

def prime (i : Bond f) : ℝ :=
  ∑ j : G.ColorIndex, letterBase (Physical.windows S d.betaHat) (beam d.tube k V d.betaHat A F) (i,j)

def essay (i : Letter (Bond f) 1) : ℝ := Paint.braid (AnalyticBridge.RelativeLogdet.page
  (Physical.windows S d.betaHat) (beam d.tube k V d.betaHat A F)) i

def customs (i : Letter (Bond f) 0) : ℝ := Paint.braid (errata
  (Physical.windows S d.betaHat) (beam d.tube k V d.betaHat A F)) i

def dots : Dots f → ℝ := Sum.elim (prime d F A k V) (essay d F A k V)

def itinerary (i j : Full G f) : Sequence (Bond f)→ℝ := strand (beam d.tube k V d.betaHat A F) (cloudX d.tube d.betaHat k V A F) i j

local notation "B" => radiusB d.betaHat
local notation "s" => d.betaHat

def dark := dots d F A k V-dots d F (Push.SectorMeasure.voidStore S) k (1:Config G c)

lemma awards (h : Lit d) (hv : A.flags=RG.flags (temp s) V) :
    HasSum (dots d F A k V) (Real.log (Rows.gram d.tube s V k (shots S s) A F).det) ∧
    HasSum (customs d F A k V) (Real.log (1+(Rows.gram d.tube s V k (shots S s) A F*fog A F d.tube s V k-1)).det) ∧
    ∀ i j : Full G f, HasSum (itinerary d F A k V i j) (((Physical.CFull d.tube A F s V k)⁻¹-Physical.AFull d.tube A F s V k) i j) := by
  obtain ⟨v,C,η,b,r,hP,h0,h1⟩:=h.reception
  have hm := hP.writes F k hv
  have hc := hP.fogs F k hv
  let T:=d.tube
  let Y:=Physical.AFull T A F s V k; let Q:=Physical.CFull T A F s V k; let W:=Physical.windows S (G:=G) s
  obtain ⟨a₀,a₁,a₂,a₃⟩:=hm.contributions (l:=20) hP.small hc.2 (Physical.furnished d.tube k V h.aperture.branched A F hP.geometry) (show (0:ℝ) ≤ 0 from le_refl _) h1 h0
  rw [Physical.a_det ..] at a₂
  rw [hP.excessive F k hv] at a₃
  obtain ⟨a,hA⟩:=h.earns A F _ hv
  have ha : beam d.tube k V s A F=Y := beam_exact _ _ _ _ _ _ h.aperture hA
  refine ⟨?_,?_,fun i j=>?_⟩
  · have hl := Paint.reconciling a₀
    rw [a₂,Fintype.sum_prod_type]; unfold dots
    refine HasSum.sum ?_ ?_
    · unfold prime; rw [ha]; exact hasSum_fintype _
    unfold essay; rw [ha]; exact hl
  · unfold customs; rw [a₃,ha]; exact Paint.reconciling a₁
  unfold itinerary cloudX; rw [ha,hc.1]; apply Notify.strands hm.kernel ?_ hm.rate ((zero_le_one.trans hm.paid)) hm.coupon hP.small hm.gram (hc.1 ▸ hc.2) i j
  have he := hm.mix
  unfold excess at he
  rwa [hc.1] at he

private lemma wide_select {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]
    (C D : Gaussian.Table ι) (e : (ι ⊕ κ) ≃ τ) (h : IsUnit C.det) (i j : ι) :
    (((Completion.wide C (1:Gaussian.Table κ)).submatrix e.symm e.symm)⁻¹ -
        (Completion.wide D (1:Gaussian.Table κ)).submatrix e.symm e.symm) (e (.inl i)) (e (.inl j))=(C⁻¹-D) i j := by
  rw [Matrix.inv_submatrix_equiv,Completion.wide_id_inv (β:=κ) C h]; simp only [Matrix.sub_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]; rfl
/-- Exact receipts for Log prices. -/
def packets (h : Lit d) : (chosen d F k₀ A k).Slices where
  paired V := number (dark d F A k V)
  limitPay V := number (customs d F A k V)
  difference V i j := number (itinerary d F A k V (active s A F i) (active s A F j))
  common V hc := by
    obtain ⟨v,C,η,b,r,hP,h0,h1⟩:=h.reception
    have hv := (awards d F A k V h hc.flags).1
    have hB := h.aperture.branched
    have he := (awards d F (Push.SectorMeasure.voidStore S) k 1 h (Export.no_seeds ..)).1
    obtain ⟨u,hu⟩ := h.valid.funds
    obtain ⟨n,l,hf,hl⟩ := hu.feeds
    rw [(Export.normal hP F k hB).2,Native.shared d.tube F F k s hf hB k₀] at he
    exact numbered (hv.sub he)
  logarithm V hc := numbered ((awards d F A k V h hc.flags).2.1)
  correction i j V hc := by
    change Rows.In (G:=G) d.betaHat A F at i j
    apply numbered
    let e := active s A F (G:=G)
    have ht := (awards d F A k V h hc.flags).2.2 (e i) (e j)
    let C := fog A F d.tube s V k
    let f₀ := Completion.sorted (G:=G) (x:=s) A F
    let J₀:= Rows.gram d.tube s V k (shots S s) A F
    have hi : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hc.kernel.isUnit
    have hh : ((Physical.CFull d.tube A F s V k)⁻¹-Physical.AFull d.tube A F s V k) (e i) (e j)=(C⁻¹-J₀) i j := by
      -- align any differing DecidableEq via congr!
      convert! wide_select C J₀ f₀ hi i j using 1
    rw [hh] at ht; exact ht
end service
end YM.PhysicalNext.Dictionary.Notify
