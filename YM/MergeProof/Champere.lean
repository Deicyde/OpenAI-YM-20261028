import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Integral
import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Committed
import YM.MergeProof.Fondue
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Performance
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Checkout
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.Opening
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix Source Labels
  Next.Foundations Attach
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {C : Family G} {N p d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C}

open YM.MergeProof Planned.GuardedAtom Guard
set_option quotPrecheck false
variable (i d p:ℕ)(D:Support (C.side i p)) (o:Site (C.side i p)) (u:Config G (C.side i p)→ℂ)(Zk:Keeper (C.path.rep i p i).p (C.path.rep i p i).activities)
local notation "Q"=> C.path.rep i p i
local notation "L!"=> C.localSection d
local notation "F!"=> C.labels.level d
local notation "K"=> (C.path.levels.budget i)
local notation "w"=> C.path.levels.clock.forcedAllowance i
def quicksilver (B:BudgetPoint) {n:Side}(D:Support n)(a b v:ℝ):ℝ:= B.mass D a+2*(D.card:ℝ)*Real.sqrt v*B.mass D b
include Zk
-- Regular pay on the actual discrepancy, not automatically marked. Both distances accounts.
lemma presses {c b usd score : ℝ} (h:C.Makes) (hh : C.ref d ≤ i)(z:Label G d)(hz:Reads C.params o D z u)(he:(C.localSection d).footprint o⊆D)(hd : 1 ≤ usd) (paid : ∀ (v : C.label d) (n : Side) (o : Site n) (U), ‖(C.localSection d).places v o U‖ ≤ usd*(C.labels.level d).coeffSize v)
    (hω:D.card*(C.path.levels.clock.forcedAllowance i) ≤ 1) (hr:(C.path.levels.budget i).Regular D u)(hb: 0 ≤ b)(hB:∀ U, ‖u U‖≤b) (hx:(F!).coeffSize ((F!).scaled (C.path.levels.budget i).threshold ((C.labels.level d).coords z)) ≤ score)
    (ht:(C.path.levels.budget i).supBounds o D (u-(C.localSection d).places ((C.labels.level d).coords z) o) c): let Y := badCost C d i usd score b
      ∃ P:Coefficient (F!) (C.side i p), P.x=(F!).scaled (C.path.levels.budget i).threshold ((C.labels.level d).coords z) ∧ P.Format o C.params (C.path.rep i p i) ∧ (∀ U,P.density o L! Q U=((C.path.rep i p i).eval U:ℂ)*u U) ∧ P.remBound o Q (Real.sqrt w) (quicksilver K D c Y w) ∧ ∃ f,Attainment (C.path.rep i p i).p o f (Local.reservedMass K D Y) ∧ profile (C.path.rep i p i).activities P.forced=hook (C.path.rep i p i).activities (C.path.rep i p i).p.threshold f:=by
  intro Y
  let F:= F!
  let R:= Q
  let B:= K
  let X := C.localSection d
  let V := C.path.levels
  let x := F.scaled B.threshold (F.coords z)
  let A := X.footprint o
  let q := B.threshold
  let v := F.scaled q⁻¹ x
  have hv : v=F.coords z := by
    simpa only [x, v, inv_inv] using
      F.scaled_inv (show q⁻¹≠0 from inv_ne_zero B.threshold_pos.ne') (F.coords z)
  let g := X.places v o
  let ξ := X.places (F.scaled q⁻¹ (F.core x)) o
  have hg := section_bounds C d i p h hh o x
  have hξ := section_bounds C d i p h hh o (F.core x)
  -- Residual u-g null in raw region. Wrapping allowed in this lemma (D
  -- contains the FOOTPRINT, which itself is nonwrapping).
  let y := u-g
  have hy : y 1=0 ∧ (Nonwrapping D o → C.params.PiVanish d o y) := by
    have hw := placed_reads X o (h.places _ i p hh) (h.sections _) v
    rw [show F.coords.symm v = z from hv ▸ F.coords.symm_apply_apply _] at hw
    have hj : Reads C.params o D z g := by
      unfold Reads
      split
      · rw [Reads, if_pos (nonwrapping_placement X o (h.places _ i p hh))] at hw
        exact hw
      next hq =>
        rw [Reads, if_neg hq] at hz
        unfold g
        rw [hz, hv,hz, map_smul,F.coords_unit]
        simp only [SectionData.places,X.eval_linear.map_smul, show X.evaluate F.e0=1 from (h.sections _).unit]
        simp
    apply (reads_null_iff C.params d o D _).1
    exact sub_self z ▸ reads_sub hz hj
  let a := (C.path.levels.params i).columns
  have hm : B.Regular D g := regular_larger hg.1 he
  have hs : B.Regular D y := regular_sub hr hm
  have hg' (U) : g U=x 0+ξ U := by
    have hw : x=x 0 • F.e0 + F.core x := by
      ext1 j; by_cases e:j=0
      · subst j; simp [Frame.e0,Frame.core]
      simp [Frame.e0,Frame.core,e]
    calc
      g U = X.evaluate (F.scaled q⁻¹ (x 0 • F.e0 + F.core x)) (expandAt o U) := congr_arg (fun v => X.places (F.scaled _ v) o U) hw
      _ = _ := by
        rw [map_add,map_smul,F.scaled_unit, X.eval_linear.map_add,X.eval_linear.map_smul,
          show X.evaluate F.e0=1 from (h.sections _).unit]; simp; rfl
  let bad := y - masked q D y + (ξ - masked q A ξ)
  have hw : ∀ U,Healthy q D U → bad U=0 := by
    intro U hp; unfold bad; simp only [Pi.add_apply,Pi.sub_apply,masked_eq _ _ _ _ hp,
        masked_eq _ _ _ _ (show Healthy q A U from Finset.disjoint_of_subset_left he hp),sub_self,add_zero]
  let Z := usd*seats C d i*score
  have hC : 0 ≤ usd := zero_le_one.trans hd
  have hZ (v : F.Coeff) (hv : F.coeffSize v ≤ score) U :
      ‖X.places (F.scaled q⁻¹ v) o U‖ ≤ Z := by
    refine (paid _ _ _ _).trans ((mul_le_mul_of_nonneg_left (sits C d i v) hC).trans ?_)
    rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left hv (mul_nonneg hC (seats_nonneg ..))
  have h₀ : 0 ≤ Y := add_nonneg hb (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hC) (seats_nonneg ..)) ((coeff_pos F x).trans hx))
  have hY (U) : ‖bad U‖ ≤ Y := by
    have he (X : Support _) (v : Config G (C.side i p) → ℂ) : ‖(v-masked q X v) U‖ ≤ ‖v U‖ := by
      by_cases h : Healthy q X U <;> simp [h]
    apply (norm_add_le ..).trans
    apply (add_le_add ((he _ y).trans (norm_sub_le ..)) (he _ ξ)).trans
    apply (add_le_add (add_le_add (hB U) (hZ x hx U)) (hZ (F.core x) ((core_price F x).trans hx) U)).trans_eq
    unfold Y Z badCost; ring
  have hv' : R.p=B := (h.wilson.represents i p i le_rfl).vac
  have hz : q=R.p.threshold := by rw [hv']
  have hr' := (h.wilson.represents i p i le_rfl).good.labels
  have ho : o∈D := he (Finset.mem_image.mpr ⟨0,(h.sections _).anchored,by simp⟩)
  have hc : Slots.Proper D bad R.p.threshold := by
    have hA := proper_gap B D y hs; have hD := proper_gap B A ξ hξ.1
    rw [hv']; refine ⟨?_,?_,hA.measurable.add hD.measurable⟩
    · exact fun U V ha hb => congr_arg₂ (· + ·) (hA.local_ U V ha hb) (uses_larger hD.local_ he U V ha hb)
    exact fun t U => congr_arg₂ (· + ·) (hA.gauge t U) (hD.gauge t U)
  have hT:R.p.supBounds o D y c:= by rw [hv']; simpa only [y,g,hv] using ht
  have hf : Push.Local.Attaches R.p.threshold D bad:=⟨hc.local_,hc.gauge,hc.measurable,fun U=>hz ▸ hw U⟩ -- hw shadow
  have hq (U):Extra.Histories.part X o R U x+masked R.p.threshold D y U+bad U=u U:=by
      change x 0+_+_+_=u U -- expand
      change x 0+masked _ _ _ _+_+_=u U; simp only [hv']
      change x 0 + masked q A ξ U + masked q D y U + ((y U - _) + (ξ U - _)) = u U
      rw [show y U = u U - (x 0 + ξ U) from congr_arg (u U-·) (hg' U)]; abel
  obtain ⟨W,hp,hF,hV,hE,f',hf',hq'⟩:= platter R Zk C.params X (h.wilson.represents i p i le_rfl|>.good) (show 0<w from Real.exp_pos _) hω (hv'.symm ▸ hs) hT hy.1 hy.2 ho hf h₀ hY hq
  -- prices only
  refine ⟨W,hp,hF,hV,?_,f',?_,hq'⟩
  · exact (show R.p.mass D c+2*(D.card:ℝ)*Real.sqrt w*R.p.mass D Y=quicksilver K D c Y w from by rw [hv']; rfl) ▸ hE
  exact stackFee hf' (le_of_eq (by rw [hv']))
end YM.Push.RelayDifference.Opening
