import YM.Next.EXTRACTION.Base
import YM.Push.RELAY_MARK.Budget
import YM.Push.RELAY_MARK.Heredity


/-!
# Can choose to solve transit here too

An option already at RAuthors, alongside the mark delivery. Transit
here is for arbitrary `dollar` arrays even j-dependent. To get the
real `RelayCosts` it will then suffice to deliver just `pace` from
matching (on the same data). -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Labels Wilson Source Lattice RG Bid Next.Extract Extraction.Lease
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d e : ℕ} {R : Weave G}

-- Slip at RAuthors. All T from one choice. More than our earlier Portfolio.
def Agreed (G : Gauge) (H : Hol G) (f : Frames G) (T : ∀ d,SectionData (f.level d)) (R : Weave G) :=
    (∀ d, Portfolio H (T d) (R d)) ∧ ∀ d p,
      (T d).evaluate ((f.level d).coords (R d p)) =
        (T (d+1)).evaluate ((f.level (d+1)).coords (R (d+1) (bud G d p)))



lemma accord_all (h : Agreed G C.params C.labels C.localSection R) (p : Label G d) (hv : d≤e) :
    (C.localSection d).evaluate ((C.labels.level d).coords (R d p)) =
      (C.localSection e).evaluate ((C.labels.level e).coords (R e (raiseLabel G hv p))) := by
  induction e,hv using Nat.le_induction with
  | base => rfl
  | succ e he ih => rw [ih]; exact h.2 e (raiseLabel G he p)

variable (C) (R)

def song (C : Family G) (h : d≤e) (R : Weave G) :=
    (((C.labels.level e).coords.toLinearMap ∘ₗ (R e).toLinearMap) ∘ₗ (raiseLabel G h)) ∘ₗ
      ((R d).symm.toLinearMap ∘ₗ (C.labels.level d).coords.symm.toLinearMap)

def ringed (h : d ≤ e) (x : Rowe C d) : Rowe C e := fun j=>
    ((C.S.a j.1:ℂ)^(e-d)) • embedTo C R e j.1 j.2 (raiseLabel G h ((embedTo C R d j.1 j.2).symm (x j)))

variable {C R}

private lemma recording (x : Rowe C d) (i) : writing C d x i =
    (C.labels.level d).coords (R d ((embedTo C R d i.1 i.2).symm (x i))) := by
  simp [embedTo,writing]

private lemma ringed_writing (C : Family G) (R : Weave G) (h : d≤e) (x : Rowe C d) (j) : writing C e (ringed C R h x) j=
    ((C.S.a j.1:ℂ)^(e-d)) • song C h R (writing C d x j) := by
  simp only [song, recording (R:=R), ringed, map_smul, LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

lemma moves_exact (h : d≤e) (he : Agreed G C.params C.labels C.localSection R) (x : Rowe C d) :
    upper C (ringed C R h x)=upper C x := by
  funext N p o
  have ht := normal (ringed C R h x) N p o
  rw [ringed_writing C R h x] at ht
  have hk := normal x N p o
  let V := upper C x N p o
  let z := ((embedTo C R d N p).symm (x (N,p)))
  let a := (C.S.a N:ℂ)
  have ha : a≠0 := Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'
  have hm : song C h R (writing C d x (N,p))=(C.labels.level e).coords (R e (raiseLabel G h z)) := by simp [song,recording (R:=R),z]
  have hg : writing C d x (N,p)=(C.labels.level d).coords (R d z) := recording _ _
  apply smul_right_injective _ (pow_ne_zero e ha)
  change (C.S.a N:ℂ)^e • upper C (ringed C R h x) N p o=(C.S.a N:ℂ)^e • upper C x N p o
  rw [ht,hm, show (C.S.a N:ℂ)^e=(C.S.a N:ℂ)^(e-d) * (C.S.a N:ℂ)^d by rw [← pow_add,Nat.sub_add_cancel h],mul_smul,hk,hg]; funext U
  unfold SectionData.places; simp only [(C.localSection e).eval_linear.map_smul,Pi.smul_apply]
  rw [accord_all he z h]

lemma preserves_fee (h : d≤e) (R : Weave G) {x : Rowe C d} {F : Extraction.Order} (he : dollar C F x) :
    dollar C F (ringed C R h x) := by
  rw [dollar_iff]
  let L := (song C h R).toContinuousLinearMap
  have hv := ((Score.const C.S F ‖L‖).mul ((dollar_iff _).1 he) (Eventually.of_forall fun i=> norm_nonneg _))
  apply hv.easier; refine Eventually.of_forall fun i=>?_
  rw [ringed_writing,norm_smul]
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (L.le_opNorm _)
  rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le];
  apply pow_le_one₀ (C.S.a_pos _).le; rw [← C.S.a_zero]; exact C.S.strictAnti.antitone (Nat.zero_le _)

structure Packaged (C : Family G) (R : Weave G) : Prop where
  made : C.Makes
  sign : Agreed G C.params C.labels C.localSection R



lemma Packaged.arrays (h : Packaged C R) (F : Extraction.Order) (he : d ≤ e) (x : Rowe C d)
    (hv : dollar C F x) : vet C F e (upper C x) :=
    ⟨ringed C R he x, preserves_fee he R hv,by rw [moves_exact _ h.sign,sub_self]; exact rent_zero C F⟩

lemma Packaged.travel (h : Packaged C R) (F : Extraction.Order) (he : d ≤ e) (x : C.label d) :
    vet C F e (Bid.visits C d x) := h.arrays F he _ (from_ref h.made (d:=d) (fun _=>x) (Score.const C.S F ‖x‖))


end YM.Push.Mark
