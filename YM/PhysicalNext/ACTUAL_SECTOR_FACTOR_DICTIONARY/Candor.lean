import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Ground
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Occasion

/-! Restore prior to reconnection any intact history on the incoming
marker and K alphabet. Do not, for example, represent an insertion by
a ratio on a zero-price K. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Formal
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.PhysicalNext.Dictionary.Formal
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment Lobbies SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (h : Lit D) (F : Forest S.ratio) (A : Stores S) (k₀ k : S.Choices) (V : Config G c) (Z : Art I D) (H : Shipment.Valid D I Z) (s : ℝ) (m : Finset I)
    (i : Head I)
local notation "H₀"=>chosen D F k₀ A k
local notation "b₀"=>team i
local notation "R₀"=>D.input
variable (U : Config G f)

def edition (j : ℕ) : ℂ := match lookup i j with
  | none => ↑(D.labels.K j U)
  | some l=> Z.essay j l U

def outward : ℂ := (∏ j∈coin i, Z.units j) * ∏ j∈menu i,masked D.input.p.threshold (Z.plot j) (Z.score j) U

def introits : Prop := Formal.signal D Z i m ∧ Fleet.pure Prod.fst (torn i) ∧
    ((∀ j∈menu i,(Z.names j).Nonempty) ∧ ∀ j∈torn i,j.1∈team i ∧ (Z.sig j.1 j.2).Nonempty)

def caption : ℂ := if introits D Z m i ∧ D.labels.admissible D.input.p U (team i) then
    (Real.exp (D.input.exponent U) : ℝ) * outward D Z i U * ∏ j∈team i,edition D Z i U j else 0

include h H
private lemma studied (j : ℕ) (he : edition D Z i U j ≠0) : (D.labels.forced j).eligible D.input.p.threshold U := by
  unfold edition at he; split at he
  · obtain ⟨_,_,_,_,_,h₁⟩:=h.valid.lawful
    exact h₁.labels.forced.permit j U (fun hf=>he (hf ▸ Complex.ofReal_zero))
  exact H.heads _ _ U he

lemma readings (h₁ : D.Nonoverlap b₀) :
    (∏ j∈team i,edition D Z i U j) * (↑(∏ x,D.qVoid (team i) x U) : ℂ)=
      if D.labels.admissible D.input.p U b₀ then (∏ j∈team i,edition D Z i U j) else 0 := by
  rw [D.qProd]; split_ifs with hx hy hy <;> simp
  · -- coverage but not admissible means K product zero from eligible
    by_contra! hz
    apply hy
    refine ⟨h₁, ?_⟩
    have ht j (hj:j∈team i) := (studied D h Z H i U j (Finset.prod_ne_zero_iff.mp hz j hj)).1
    ext x; rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨j,hj,he⟩; exact (Finset.mem_inter.mp ((ht j hj).symm ▸ he)).2
    intro hl; obtain ⟨j,hj,hv⟩:=Finset.mem_biUnion.mp (hx hl)
    exact ⟨j,hj,((ht j hj) ▸ Finset.mem_inter.mpr ⟨hv,hl⟩)⟩
  apply False.elim; apply hx
  intro j hj; obtain ⟨u,hu,he⟩ := Finset.mem_biUnion.mp (show j∈ (b₀).biUnion (fun i=>(D.labels.forced i).inventory) by rwa [hy.2])
  exact Finset.mem_biUnion.mpr ⟨u,hu,(D.labels.forced u).inventory_sup he⟩

variable (hp : A.flags=RG.flags (temp D.betaHat) V)

include hp
private lemma uncovered (uPAGE : (H₀).Visual) : skin D F A (team i) k V (Print.backdrop D.betaHat A F uPAGE)=(H₀).hard V uPAGE := by
  obtain ⟨C,hC⟩:=h.earns A F V hp; obtain ⟨η,hη,hP⟩:=h.gaps A F V k hp
  have he := Print.painted D.tube D.betaHat D.broadCut D.radius D.g k V h.aperture hC hη hP (Print.backdrop D.betaHat A F uPAGE)
  -- specify
  calc _ = (H₀).hard V (Print.see D.betaHat A F (Print.backdrop D.betaHat A F uPAGE)) :=he
       _ = _:=by rw [Print.rollback]

-- Only claim this after reassembling all tests including broad. No gamma identities needed other than together!
omit hp in
private lemma lights (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (ht : (∏ j,exam D F A k₀ k V (team i) uPAGE j) ≠ 0) :
    let p:=Print.backdrop D.betaHat A F uPAGE
    let U₀ := (H₀).hard V uPAGE
    (∑ v:Versions i, lamps D F A k V Z s i v p)= outward D Z i U₀ * ∏ j∈b₀, edition D Z i U₀ j := by
  intro p U₀
  have hb:=coat_cost D h F A k₀ k V b₀ uPAGE hc ht
  have hs : skin D F A b₀ k V p=U₀ := uncovered D h F A k₀ k V Z H i hc.flags uPAGE
  have he (j : menu i) : ∑ v:Bool, choices D Z s (bead j v) F A b₀ k V p = masked D.input.p.threshold (Z.plot j) (Z.score j) U₀ := by
    rw [Fintype.sum_bool]; simp only [choices,bead]
    unfold total; rw [hs]
    simp [show ∀ s,tarp D s F A b₀ k V p = 1 from hb]
  have hm (j : ℕ) : job D Z j (lookup i j) F A b₀ k V p = edition D Z i U₀ j := by
    unfold job edition; cases lookup i j <;> dsimp only
    · change (↑(D.labels.K _ (skin D F A b₀ k V p)* _) : ℂ)=_
      rw [hs,hb,mul_one]
    rw [hs,hb,Complex.ofReal_one,mul_one]
  unfold lamps; rw [← Finset.mul_sum]
  change (_*_)*(∑ v:(↥(menu i)→Bool),∏ j:menu i, choices D Z s (bead j (v j)) F A b₀ k V p)=_
  rw [← Fintype.prod_sum (f:=fun (j : menu i) (t : Bool)=>choices D Z s (bead j t) F A b₀ k V p)]; simp_rw [he,hm]
  unfold outward; rw [Finset.prod_coe_sort (menu i) (fun j : ℕ=>masked D.input.p.threshold (Z.plot j) (Z.score j) U₀)]; ring

-- Report equality on every Head, even ones that miss the seed packets or only at sites where a tagged signal is zero.
-- H.assembled will then sum over all Stations without adding a mode filter.
omit hp in
theorem report (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) :
    (if welcomes D A Z i m then
        (∑ v:Versions i, lamps D F A k V Z s i v (Print.backdrop D.betaHat A F uPAGE)) *
          (↑((∏ j,exam D F A k₀ k V (team i) uPAGE j)*Real.exp ((H₀).sumValue V uPAGE)):ℂ)
      else 0) = ↑(Ground.staple D F k₀ k V A uPAGE) * caption D Z m i ((H₀).hard V uPAGE) := by
  let X:=(H₀); let U₁:=X.hard V uPAGE
  let C₀:=Ground.staple D F k₀ k V A uPAGE; let M:=Real.exp (X.sumValue V uPAGE); let c' := Real.exp ((R₀).exponent U₁)
  let v:=∏ j : X.TestIndex,X.test V uPAGE j
  let q:=∏ x, D.qVoid b₀ x U₁
  let r:=∏ j∈b₀,edition D Z i U₁ j
  let d:=outward D Z i U₁
  let a:=∑ t:Versions i, lamps D F A k V Z s i t (Print.backdrop D.betaHat A F uPAGE)
  have ht : C₀ * c' = v*M := by
    let v₁ (_:S.Choices) (u : Config G f):=Real.exp (D.input.exponent u)
    rw [mul_comm]; exact (Ground.real_body D F k₀ k V A v₁ uPAGE).symm.trans (Ground.initial D h F k₀ k V A hc.flags uPAGE)
  have hq : (∏ j,exam D F A k₀ k V b₀ uPAGE j) = v*q := Fintype.prod_sum_type _
  change (if welcomes D A Z i m then a*(↑(_*M):ℂ) else 0)= (↑C₀:ℂ) * (if introits D Z m i ∧ D.labels.admissible (R₀).p U₁ (team i)
    then ↑c'*d*r else 0)
  rw [hq]; split_ifs with he hz hz
  · -- both. K & q coverage conserved
    have ho := he.2.1 -- origins
    have hr : r*(↑q:ℂ)=r := (readings D h Z H i U₁ ho.1).trans (if_pos hz.2)
    by_cases hl : v*q ≠ 0
    · rw [show a=d*r from lights D h F A k₀ k V Z H s i uPAGE hc (by rwa [hq])]
      calc _ = (r * (↑q:ℂ)) * d * (↑(v*M):ℂ) := by push_cast; ring
           _ = _:= by rw [hr, ← ht]; push_cast; ring
    rw [not_not.mp hl,zero_mul]
    rw [show ((↑C₀:ℂ)*(↑c'*d*r))=( (↑(v*M):ℂ) * d * r) from by rw [← ht]; push_cast; ring]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero (of_not_not hl) with h1|h2
    · rw [h1]; simp
    rw [h2,Complex.ofReal_zero,mul_zero] at hr; simp [←hr]
  · -- welcomed but not admitted ⇒ q or a K kills; tarp/gate zero kills
    have ho:=he.2.1
    have hy : ¬ D.labels.admissible (R₀).p U₁ b₀ := fun h1 => hz ⟨⟨he.1,he.2.2⟩,h1⟩
    have hr : r*(↑q:ℂ)=0 := (readings D h Z H i U₁ ho.1).trans (if_neg hy)
    rw [mul_zero]; by_cases hl : v*q ≠0
    · have hu : (↑((v*q)*M):ℂ)= (↑q:ℂ)*↑(v*M) := by push_cast; ring
      rw [show a=d*r from lights D h F A k₀ k V Z H s i uPAGE hc (by rwa [hq]),hu]
      calc _ = d*(r*↑q)*↑(v*M) := by ring
           _ = _ := by rw [hr]; ring
    rw [of_not_not hl]; simp
  · -- admissible but origins absent. `staple` still carries D.bill. Link via ht and ⇒ profile bill ≠0.
    by_cases hv : v=0
    · rw [show (↑C₀:ℂ)*(↑c'*d*r)= (↑(v*M):ℂ)*d*r from by rw [←ht]; push_cast; ring, hv]; simp
    apply False.elim; apply he
    refine ⟨hz.1.1, ⟨hz.2.1,fun j hj x hx=>?_⟩, hz.1.2⟩
    obtain ⟨a,ho₁⟩:=h.valid.funds
    have hb := (H₀).checked_at V hc.flags uPAGE
    change v= _ *((Next.SectorChange.doors ..)*D.allocation.bill _ _ _ _*_ ) at hb
    rw [hb] at hv
    apply Allocation.flagged D.allocation (right_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul hv))) x
    rw [←h.valid.same.temp]; change x∈ RG.flags _ U₁; rw [←hz.2.2]
    exact Finset.mem_biUnion.mpr ⟨j,hj,hx⟩
  simp
end YM.PhysicalNext.Dictionary.Formal
