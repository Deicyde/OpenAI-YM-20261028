import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis
import YM.PertExtension.MixedRule
import YM.Next.FOUNDATIONS.Primary

/-! Choice of on-shell axes from the given reference frames, representable at
each bare column's own horizon before position frame matching. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace YM.PertExtension.Horizon
open Filter Set Labels Function Wilson Lattice Gauge Precision RG Source Extra.FD Next.Foundations
open scoped Topology BigOperators ContDiff Classical
open LatticePT
variable {G : Gauge}{d e : ℕ}

lemma reference_rises (F : Frames G)(h : e ≤ d)(v : (F.level e).Index) :
  ∃ i, raiseLabel G h ((F.level e).basis v) = (F.level d).basis i := by
  induction d, h using Nat.le_induction with
  | base=> exact ⟨v,rfl⟩
  | succ d h ih =>
    obtain ⟨i,hi⟩:=ih
    obtain ⟨j,hj⟩:=F.coherent _ ⟨i,rfl⟩
    exact ⟨j,(congr_arg (raiseLabel G (Nat.le_succ d)) hi |>.trans hj.symm)⟩

def lowered (F : Frame G d) (i:F.Index) : Label G (F.grades i).1 :=
  ⟨(F.basis i).val,
    (by refine ⟨?_,(F.basis i).property.2⟩
        change _ ∈ limited G _
        rw [limited,MvPolynomial.mem_restrictSupport_iff]
        intro p hp
        change height p ≤ _
        refine le_of_eq ?_
        exact (congr_arg Prod.fst (weight_slot p)).symm.trans (congr_arg Prod.fst ((pure_grade _ _).1 (F.pure i) (MvPolynomial.mem_support_iff.mp hp))) )⟩

lemma reascend (F:Frame G d) (i:F.Index) :
    raiseLabel G (F.bound i) (lowered F i) = F.basis i := rfl

lemma counterpart (F : Frames G)(i:(F.level d).Index) :
    let K:=F.level d; let j:=(K.grades i).1
    ∃ v : (F.level j).Index, (F.level j).basis v=lowered K i ∧ (F.level j).grades v=K.grades i := by
  intro K j; let U:=F.level j
  choose ζ hζ using reference_rises F (K.bound i)
  let v:=lowered K i
  have hh : ∑ x:U.Index,(U.basis.repr v x) • K.basis (ζ x)=K.basis i := by
    calc
      _ = ∑ x, (raiseLabel G (K.bound i)) ((U.basis.repr v x) • U.basis x) := Finset.sum_congr rfl fun x _=> by rw [map_smul,hζ x]
      _ = _ := by rw [←map_sum,Module.Basis.sum_repr]; exact reascend K i
  suffices ∃ t,ζ t=i by
    obtain ⟨t,ht⟩:=this
    have hm : U.basis t=v := Subtype.ext (congr_arg (fun x : Label G d=>x.val) ((hζ t).trans (congr_arg K.basis ht)))
    exact ⟨t,hm,pure_unique (by rw [←hm];exact U.basis.ne_zero t) _ _ (hm ▸ U.pure t) (show v∈Grade (K.grades i) from K.pure i)⟩
  by_contra! he
  have h := congr_arg (fun x=>K.coords x i) hh
  simp only [map_sum, map_smul,Finset.sum_apply,K.coords_basis] at h
  simp [Pi.single_eq_of_ne (Ne.symm (he _))] at h

section axes
variable (F : Frames G) (d)
def reference (t : Fin ((recorded F d).m+1)) := ((recorded F d).corners t).choose
def weight (t : Fin ((recorded F d).m+1)) := ((F.level d).grades (reference (F:=F) d t)).1
def sourceAxis (t : Fin ((recorded F d).m+1)) := (counterpart F (reference (F:=F) d t)).choose
lemma source_match (t) : raiseLabel G ((F.level d).bound (reference (F:=F) d t)) ((F.level (weight (F:=F) d t)).basis (sourceAxis (F:=F) d t))
    =(F.level d).basis (reference (F:=F) d t) := by
  unfold weight
  unfold sourceAxis; rw [(counterpart F (reference d F t)).choose_spec.1,reascend]

def word (H : Hol G)(S : ∀ n, SectionData (F.level n)) (hS : ∀ n,(S n).Sound H)(pop : ∀ n,Bid.pop (S n))(t : Fin ((recorded F d).m+1)) : Word G :=
  ⟨weight (F:=F) d t, _,S _,H,hS _,pop _,sourceAxis (F:=F) d t,
    congr_arg Prod.fst ((counterpart F (reference (F:=F) d t)).choose_spec.2)⟩

def constructionWord (t : Fin ((recorded (frames G) d).m+1)) : Word G :=
  word (F:=frames G) d (hol G) (localSection G) (sound G) (valuation G) t

end axes
end YM.PertExtension.Horizon
