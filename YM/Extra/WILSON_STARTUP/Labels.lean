import YM.Extra.WILSON_STARTUP.Packets

/-! # One startup dictionary, including dormant E, forced and attachment addresses -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Start
open Function Filter RG Wilson Lattice Design Work Ovens Pipes Padded Ac
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}

abbrev Blank (n : Side) := {x : Site n × Support n // x.1 ∈ x.2}
abbrev Foot (n : Side) := {x : Support n × Support n // x.2.Nonempty ∧ x.2 ⊆ x.1}
abbrev Sheet (n : Side) := Key n ⊕ Blank n
abbrev Reach (n : Side) := {x : Support n // x.Nonempty}

scoped instance blankNonempty : Nonempty (Blank n) := ⟨⟨(0,{0}),Finset.mem_singleton_self _⟩⟩
scoped instance footNonempty : Nonempty (Foot n) := ⟨⟨({0},{0}),Finset.singleton_nonempty _,Finset.Subset.refl _⟩⟩
scoped instance reachNonempty : Nonempty (Reach n) := ⟨⟨{0},Finset.singleton_nonempty _⟩⟩

def supports (s : Signed) (x : Site n) := (frameSites s x).finsetCongr

lemma supports_apply (s : Signed) (x : Site n) (D : Support n) : supports s x D = D.image (affine s x) := by
  unfold supports; rw [Equiv.finsetCongr_apply,Finset.map_eq_image]; rfl

def blankAction (s : Signed) (x : Site n) : Equiv.Perm (Blank n) :=
    Equiv.Perm.subtypePerm ((frameSites s x).prodCongr (supports s x)) (by
      intro p
      change affine s x p.1 ∈ supports s x p.2 ↔ _
      rw [supports_apply]; simp [(aff_inj s x).eq_iff])

def sheetAction (s : Signed) (x : Site n) : Equiv.Perm (Sheet n) :=
    (Key.perm s x).sumCongr (blankAction s x)

def footAction (s : Signed) (x : Site n) : Equiv.Perm (Foot n) :=
    Equiv.Perm.subtypePerm ((supports s x).prodCongr (supports s x)) (by
      intro p
      change ( (supports s x p.2).Nonempty ∧ supports s x p.2 ⊆ supports s x p.1) ↔ _
      simp [supports_apply,Finset.image_subset_image_iff (aff_inj ..)])

def reachAction (s : Signed) (x : Site n) : Equiv.Perm (Reach n) :=
    Equiv.Perm.subtypePerm (supports s x) (by intro p; rw [supports_apply]; simp)

def eInfo (i : Sheet n) : RegularAddress n := i.elim Key.addrE (fun p => ⟨p.val.1,p.val.2,p.property⟩)
def kInfo (G : Gauge) (i : Foot n) : ForcedAddress G n := ⟨i.val.1,i.val.2,i.property.1,i.property.2,fun _ => True⟩

@[simp] theorem eInfo_transport (s : Signed) (x : Site n) (i : Sheet n) :
    eInfo (sheetAction s x i) =
      ⟨affine s x (eInfo i).site, ((eInfo i).support).image (affine s x),Finset.mem_image_of_mem _ (eInfo i).anchor⟩ := by
  cases i with
  | inl i => simp [sheetAction,eInfo,Key.addrE,Key.spun]; rfl
  | inr i =>
    simp only [sheetAction,Equiv.sumCongr_apply,Sum.map_inr,eInfo,Sum.elim_inr]
    congr 1; exact supports_apply s x _

theorem foot_trans (s : Signed) (x : Site n) (i : Foot n) :
    (footAction s x i).val = (i.val.1.image (affine s x), i.val.2.image (affine s x)) :=
    congr_arg₂ Prod.mk (supports_apply ..) (supports_apply ..)

def dictionary (G : Gauge) (n : Side) : Pipes G n where
  reg := fun i => eInfo (name (Sheet n) i)
  kernel := fun i => kInfo G (name (Foot n) i)
  softer := fun i => (name (Reach n) i).val
  sites := fun i => (name (Reach n) i).property

variable (c : Clip) (b : BudgetPoint)

def weight (β : ℝ) := β*share*bulk c

def written (i : Sheet n) (β : ℝ) : Config G n → ℝ := i.elim (fun p => weight c β • p.accrual) (fun _ => 0)
def lives (i : Foot n) := Spark (pad b) i.val.2 ∧ i.val.1 = region b i.val.2

def admission (i : Foot n) (U : Config G n) := lives b i ∧ i.val.1 ∩ flags b.threshold U = i.val.2

def paid (i : Foot n) (β : ℝ) (U : Config G n) := if admission b i U then Real.exp (-β * charge c b i.val.2 U) else 0

def payload (G : Gauge) (n : Side) (β : ℝ) : Tap G n where
  regular := fun i => if fixed (Sheet n) i then written c (name (Sheet n) i) β else 0
  forced := fun i => if fixed (Foot n) i then paid c b (name (Foot n) i) β else 0
  logarithm := 0

variable {c b}

def raw (G : Gauge) (n : Side) (c : Clip) (b : BudgetPoint) (β : ℝ) := (dictionary G n).pours (payload c b G n β)

lemma admission_iff (i : Foot n) (U : Config G n) : admission b i U ↔ lives b i ∧ (kInfo G i).eligible b.threshold U := by
  simp [admission,ForcedAddress.eligible,kInfo]

theorem paid_gauge (i : Foot n) (β : ℝ) (U : Config G n) (k : Site n → G.El) : paid c b i β (gauge k U) = paid c b i β U := by
  simp [paid,admission,charge_gauge]

theorem paid_meas (i : Foot n) (β : ℝ) : Measurable (paid c b i β (G:=G)) := by
  unfold paid; simp_rw [admission_iff]
  by_cases he : lives b i
  · simp only [he,true_and]
    exact Measurable.ite (H03.eligible_measurable _ _ MeasurableSet.univ)
      (Real.continuous_exp.measurable.comp (measurable_const.mul (charge_measurable ..))) measurable_const
  simp [he,measurable_const]

theorem paid_final (h : Decent c b) (i : Foot n) (β : ℝ) : UsesFinal b.threshold i.val.1 (paid c b i β (G:=G)) := by
  intro U V he hf
  dsimp only [paid,admission]
  by_cases ht : lives b i
  · rw [ht.2] at he hf
    simp only [ht.2,charge_final c b (G:=G) h i.val.2 U V he hf,hf]
  simp only [ht,false_and, ↓reduceIte]

theorem paid_oriented (s : Signed) (x : Site n) (i : Foot n) (β : ℝ) (U : Config G n) :
    paid c b (footAction s x i) β U = paid c b i β (pull s x U) := by
  simp only [paid,admission,lives,foot_trans,spark_transport,region_image,charge_oriented,(Finset.image_injective (aff_inj ..)).eq_iff]
  -- need one direction rewrite only
  have h := H03.eligible_send s x b.threshold U (kInfo G i) (kInfo G (footAction s x i)) (congr_arg Prod.fst (foot_trans s x i))
    (congr_arg Prod.snd (foot_trans s x i)) Iff.rfl
  simp only [ForcedAddress.eligible,kInfo, and_true,foot_trans] at h
  simp only [h]; congr 1

theorem permit_paid (i : Foot n) (β : ℝ) (U : Config G n) (h : paid c b i β U ≠ 0) : (kInfo G i).eligible b.threshold U :=
  ((admission_iff i U).mp (of_not_not (fun hh => h (if_neg hh)))).2

theorem forcedFamily (h : Decent c b) (β : ℝ) : (raw G n c b β).ForcedFamily b := by
  have he i : (raw G n c b β).K i = if fixed (Foot n) i then paid c b (name (Foot n) i) β else 0 := rfl
  refine ⟨fun i k U => ?_,fun _ _ _ => Iff.rfl,fun i => ?_,fun _ => MeasurableSet.univ, fun i => ?_, fun _ _ _ _ _ => rfl,fun i U hp => ?_⟩
  · rw [he]; split; exact paid_gauge ..; rfl
  · rw [he]; split; exact paid_meas ..; exact measurable_const
  · rw [he]; split
    · exact paid_final h _ _
    intro U V _ _; rfl
  rw [he] at hp; split at hp
  · exact permit_paid _ β U hp
  exact (hp rfl).elim

theorem written_oriented (s : Signed) (x : Site n) (i : Sheet n) (β : ℝ) (U : Config G n) :
    written c (sheetAction s x i) β U = written c i β (pull s x U) := by
  cases i with
  | inl i => change weight c β * residual G _ _ = weight c β * residual G _ _; rw [Key.oriented]; rfl
  | inr i => rfl

theorem moves (s : Signed) (x : Site n) (β : ℝ) : Nonempty ((raw G n c b β).Moves s x) := by
  refine ⟨{ ep := sends (sheetAction s x), kp := sends (footAction s x), reg_site := fun i => ?_,reg_support := fun i => ?_,
            forced_support := fun i => ?_,forced_inventory := fun i => ?_,forced_tests := fun i U => Iff.rfl,
            valuesE := fun i U => ?_,valuesK := fun i U => ?_ }⟩
  · change (eInfo _).site = affine s x (eInfo _).site
    rw [name_sends,eInfo_transport]
  · change (eInfo _).support = Finset.image _ (eInfo _).support
    rw [name_sends,eInfo_transport]
  · change (name (Foot n) _).val.1 = (name (Foot n) i).val.1.image _
    rw [name_sends,foot_trans]
  · change (name (Foot n) _).val.2 = (name (Foot n) i).val.2.image _
    rw [name_sends,foot_trans]
  · simp only [raw,pours,payload,name_sends,fixed_sends]
    split <;> first | exact written_oriented .. | exact rfl
  · simp only [raw,pours,payload,name_sends,fixed_sends]
    split <;> first | exact paid_oriented .. | exact rfl
end YM.WilsonStartup.Start
