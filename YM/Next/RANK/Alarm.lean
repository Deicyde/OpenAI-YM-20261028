import YM.Next.RANK.Bag
import YM.Next.RANK.Stretch

/-!
# Regrouping over EACH newly flagged vertex

Use site suppression (share direct loss and short squares among the true
set of flagged sites). Old K may be viewed as a finite Lifted family AFTER
legitimate packing on identical supports/fires with absolute convergence.
This step enlarges old footprints -- retain old exclusions inside mergers --
and carries eligibility at *new* τ. Do not use faked old flags on site edges:
check only at the recorded new sites with real halo access; all other old/new
flag comparisons are field identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ : Type}
variable {ζ : V→Site n} {τ t : ℝ}

def S11 (z : ℂ) : veil V := z • (1:veil V)
lemma singles (z : ℂ) : S11 (V:=V) z=Poly.send (quiet V) z := by
  apply Poly.ext; intro i; simp only [S11,Poly.part_smul,Poly.part_send,Poly.one_part]
  split<;>simp [*]

def Nreal : ℝ→+*veil V where
  toFun z := S11 (V:=V) z
  map_add' a b := by rw [Complex.ofReal_add,S11,add_smul];rfl
  map_one' := by rw [Complex.ofReal_one,S11,one_smul]
  map_zero' := by simp [S11]
  map_mul' a b := by unfold S11; rw [Complex.ofReal_mul,smul_mul_assoc, mul_smul_comm]; simp only [one_mul,smul_smul]
lemma Nprice (v : V→ℝ) (z : ℝ) : Poly.price v (Nreal z)=|z| := by
  change Poly.price v (S11 _)=_;rw [singles,Poly.solo,Complex.norm_real]; simp [Poly.toll,quiet,Census.quiet]

structure Siren (G : Gauge) (n : Side) (u : ℝ) where
  chamber : Site n→ Support n
  ample x : halo 8 {x} ⊆ chamber x
  value : Site n→ Config G n→ℝ
  rings x U : x ∉ flags u U → value x U=0
  legal x : UsesFinal u (chamber x) (value x)
  meas x : Measurable (value x)
  gauge x : GaugeInvariant (value x)
lemma Siren.marked (X : Siren G n τ) (i) : i ∈ X.chamber i := X.ample i (halo_subset _ _ (mem_singleton_self ..))

-- individual letters from optional exponent factors. permit even vacuum hits.
structure Strike (G : Gauge) (ζ : V→Site n) (t : ℝ) where
  extent : Support n
  active : extent.Nonempty
  fires : modes V
  remembers i : i∈fires.val → ζ i∈extent
  value : Config G n→ℂ
  meas : Measurable value
  inv : GaugeInvariant value
  sees : UsesFinal t extent value
  only U : Healthy t extent U → value U=0

def Strike.occ (s : Strike G ζ τ) (U) := Poly.send s.fires (s.value U)

variable (A : ι→ Lifted G ζ t) (B : κ→ Strike G ζ τ) (X : Siren G n τ)
abbrev Branch (ι κ : Type) (n : Side) := (ι⊕κ)⊕Site n

def vol (i : Branch ι κ n) : Support n := Sum.elim (Sum.elim (fun a=> halo 8 (A a).extent) (fun b=> (B b).extent)) X.chamber i
lemma vol_unit (a) : (A a).extent ⊆ vol A B X (.inl (.inl a)) := halo_subset ..
lemma vol_strong (a) : inspected (A a).extent ⊆ vol A B X (.inl (.inl a)):= inspect _

def fuel (i : Branch ι κ n) : Config G n→veil V := Sum.elim (Sum.elim (fun a U=> (A a).amount U) (fun b U=> (B b).occ U))
    (fun b U=> Nreal (X.value b U)) i

def quake (p : Finset (Branch ι κ n)) (U : Config G n) : veil V := ∏ i∈p, fuel A B X i U

def chosen (A : ι→ Lifted G ζ t) (B : κ→ Strike G ζ τ) (p : Branch ι κ n) : modes V := Sum.elim (Sum.elim (fun a=> (A a).fires) (fun b=> (B b).fires)) (fun _=> quiet V) p

def alarmCount (p : Finset (Branch ι κ n)) := p.biUnion fun i=> (chosen A B i).val

lemma fuel_tag (i) (U) : ∃ z : ℂ, fuel A B X i U=Poly.send (chosen A B i) z := by
  cases i with
  | inl i=>
    cases i with
    | inl i=> exact ⟨_,rfl⟩
    | inr v=> exact ⟨_,rfl⟩
  | inr i=> exact ⟨_,singles ..⟩
lemma remembers (x U) : Poly.send (chosen A B x) ((fuel A B X x U).part (chosen A B x))=fuel A B X x U:= by obtain ⟨z,h⟩:=fuel_tag A B X ..; rw [h];simp

private lemma checked (p U) : ∃ z,quake A B X p U=Poly.send (scene (alarmCount A B p)) z := by
  induction p using Finset.induction_on with
  | empty=> exact ⟨1,by simp only [quake,alarmCount,biUnion_empty,prod_empty,scene_nil];rfl⟩
  | @insert i p hi IH =>
    obtain ⟨z,h⟩:= IH; rw [alarmCount, quake,prod_insert hi]; unfold quake at h; rw [h,← remembers A B X i,plate_pair]; split
    · rw [biUnion_insert]; refine ⟨(fuel A B X i U).part _*z,rfl⟩
    exact ⟨0,(Poly.send_zero ..).symm⟩
lemma priced (p) (U) : Poly.send (scene (alarmCount A B p)) ((quake A B X p U).part (scene (alarmCount A B p)))=quake A B X p U := by
  obtain ⟨z,h⟩:=checked A B X p U; rw [h];simp

private lemma quake_meas (p : Finset (Branch ι κ n)) (t : modes V) : Measurable fun U => (quake A B X p U).part t := by
  induction p using Finset.induction_on generalizing t with
  | empty => simp only [quake,prod_empty];exact measurable_const
  | @insert i p hi IH=>
    unfold quake; simp only [prod_insert hi]
    change Measurable fun U=> (fuel A B X i U * quake A B X p U).part t
    have ha x : Measurable fun U => (fuel A B X i U).part x := by
      cases i with
      | inl i =>
        cases i with
        | inl i =>
          unfold fuel Lifted.amount; dsimp only [Sum.elim_inl]; simp_rw [Poly.part_send]; split
          · exact (A i).meas
          exact measurable_const
        | inr i=>
          unfold fuel Strike.occ; dsimp only [Sum.elim_inr,Sum.elim_inl]; simp_rw [Poly.part_send]; split
          · exact (B i).meas
          exact measurable_const
      | inr i=>
        change Measurable fun U=> (S11 (↑(X.value i U):ℂ)).part x; simp_rw [singles,Poly.part_send]; split
        · exact Complex.continuous_ofReal.measurable.comp (X.meas i)
        exact measurable_const
    simp_rw [Glyph.part_mul]; apply Finset.measurable_fun_sum _ fun i _=> ?_; exact (ha _).mul (IH _)

variable [DecidableEq ι] [DecidableEq κ]

def cast (p : Finset (Branch ι κ n)) := Ac.Spark (vol A B X) p ∧ p.toRight.Nonempty ∧
    (p.toLeft.toLeft:Set ι).PairwiseDisjoint fun i=> (A i).extent
abbrev Domino := { p // cast A B X p }

def Settle (p : Domino A B X) := p.val.biUnion (vol A B X)

def inside (p : Domino A B X) (U : Config G n) := Settle A B X p ∩ flags τ U=p.val.toRight ∧ p.val.toRight ∩ flags t U =
    p.val.toLeft.toLeft.biUnion (fun i=> (A i).inventory)
omit [DecidableEq ι] [DecidableEq κ] in
lemma Insites (p : Domino A B X) : halo 8 p.val.toRight ⊆ Settle A B X p := by
  intro x hx; obtain ⟨y,hy,he⟩:= halo_spec.mp hx; exact mem_biUnion.mpr ⟨.inr y,mem_toRight.mp hy,X.ample y (halo_spec.mpr ⟨_,mem_singleton_self ..,he⟩)⟩

private lemma safe (l : Support n) (t : ℝ) (X : Support n) : MeasurableSet {U : Config G n| X∩flags t U=l} := by
  rw [show {U : Config G n|X∩flags t U=l}= ⋃ p : {q : Support n // X∩q=l}, {U | flags t U=p.val} by
    ext U; simp only [Set.mem_setOf_eq,Set.mem_iUnion]; constructor
    · exact fun h=>⟨⟨_,h⟩,rfl⟩
    rintro ⟨h,v⟩; rw [v]; exact h.property]
  exact MeasurableSet.iUnion fun _=> flags_measurable_eq ..

def teat (p : Domino A B X) : Lifted G ζ τ where
  extent:=Settle A B X p
  inventory:=p.val.toRight
  needed:=p.property.2.1
  records:=fun _ h=>Insites A B X p (halo_subset _ _ h)
  fires:=scene (alarmCount A B p.val)
  remembers i hi:=by
    obtain ⟨j,hj,hp⟩:= Finset.mem_biUnion.mp hi; refine mem_biUnion.mpr ⟨_,hj,?_⟩; cases j with
    | inl j=>
      cases j with
      | inl j=> exact halo_subset _ _ ((A j).remembers i hp)
      | inr j=> exact (B j).remembers i hp
    | inr j=> exact False.elim (notMem_empty _ hp)
  value:=fun U=> if inside A B X p U then (quake A B X p.val U).part (scene (alarmCount A B p.val)) else 0
  flag U ht:= by by_contra hh; apply ht; exact if_neg fun H=> hh H.1
  meas:=Measurable.ite ((safe ..).inter (safe ..)) (quake_meas A B X p.val _) measurable_const
  only U u he hf:= by
    have hz := flags_agree t U u p.val.toRight (agrees_mono he (fun _ hx=> (Insites ..) (inspect _ hx)))
    have hq : quake A B X p.val U=quake A B X p.val u := by
      refine prod_congr rfl fun i hi=> ?_
      have hS : vol A B X i ⊆ Settle A B X p:= fun x hx=>mem_biUnion.mpr ⟨i,hi,hx⟩
      cases i with
      | inl i=>
        cases i with
        | inl i=>
          have H:= (A i).only.allReads (F:=(A i).value)
          refine congr_arg (Poly.send (A i).fires) ?_; apply H; exact agrees_mono he (fun z hZ=> hS (vol_strong A B X i hZ))
        | inr i=> exact congr_arg (Poly.send (B i).fires) (Work.H03.reads_larger hS (B i).sees U u he hf)
      | inr i=>exact congr_arg Nreal (Work.H03.reads_larger hS (X.legal i) U u he hf)
    simp only [inside,hz,hf,hq]; split_ifs <;> rfl
  inv i U := by
    have h : quake A B X p.val (Lattice.gauge i U)= quake A B X p.val U:= by
      refine prod_congr rfl fun x hx=> ?_; cases x with
      | inl x=>
        rcases x with x|x
        · exact congr_arg (Poly.send _) ((A x).inv i U)
        exact congr_arg (Poly.send _) ((B x).inv i U)
      | inr x=>exact congr_arg (fun (x : ℝ) => Nreal (V:=V) x) (X.gauge x i U)
    simp only [inside, gauge_flags, h]; split_ifs <;> rfl
omit [DecidableEq ι] [DecidableEq κ] in
lemma teat_pay (p : Domino A B X) (U) : (teat A B X p).amount U = if inside A B X p U then quake A B X p.val U else 0:= by
  unfold teat Lifted.amount; dsimp only; split_ifs
  · exact priced A B X p.val U
  exact Poly.send_zero _

end YM.Next.Rank.Alarm
