import YM.Next.RANK.Bounty
import YM.Next.RANK.Charade
import YM.Next.RANK.GlyphRise

/-! Vacuum value ledger follows from Empty marker port + honest real charge.
    Use SAME flags and Camp even for padding. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ : Type}
variable (ζ : V→Site n) {τ t : ℝ}
variable (A : ι→ Burst G n t) (B : κ→ Strike G ζ τ) (X : Siren G n τ)

structure Wickless (G : Gauge) (n : Side) (τ : ℝ) where
  extent : Support n
  active : extent.Nonempty
  value : Config G n→ℝ
  inv : GaugeInvariant value
  meas : Measurable value
  sees : UsesFinal τ extent value
  untouched U : Healthy τ extent U → value U=0

def Wickless.credit (W : Wickless G n τ) : Strike G ζ τ where
  extent := W.extent
  active := W.active
  fires := quiet V
  remembers i h:=False.elim (notMem_empty i h)
  value:=Complex.ofReal ∘ W.value
  meas:= Complex.continuous_ofReal.measurable.comp W.meas
  inv i U:= congr_arg Complex.ofReal (W.inv i U)
  sees U V a b:= congr_arg Complex.ofReal (W.sees U V a b)
  only U hh:= (congr_arg Complex.ofReal (W.untouched U hh)).trans Complex.ofReal_zero
lemma vacant (W : Wickless G n τ) (U) : (W.credit ζ).occ U=Nreal (W.value U):= (singles _).symm

def enroll (A : Burst G n t) : Lifted G ζ t where
  extent:= A.city.val.1
  inventory:= A.city.val.2
  needed:= A.city.property.1
  records:= A.city.property.2
  fires:=quiet V
  remembers i h:=False.elim (notMem_empty i h)
  value U:= (A.value U:ℂ)
  meas:=Complex.continuous_ofReal.measurable.comp A.meas
  inv k U:= congr_arg Complex.ofReal (A.inv k U)
  only U v a b:= congr_arg Complex.ofReal (A.uses U v a b)
  flag U he:= A.flag U (fun h=> he (by rw [h,Complex.ofReal_zero]))
lemma enrolment (p : Finset ι) (U) : Lifted.pack (enroll ζ ∘ A) p U=Nreal (placed A p U) := by
  by_cases hx : ripe (fun i=> (A i).city) p (flags t U)
  · rw [placed,Lifted.pack,peeled, if_pos hx, if_pos (show Lifted.gather (enroll ζ ∘ A) p U from hx),map_prod]; exact prod_congr rfl fun i _=> (singles _).symm
  rw [placed,Lifted.pack,peeled,if_neg hx,if_neg (show ¬ Lifted.gather (enroll ζ ∘ A) p U from hx),map_zero]
lemma sturdy (H : Rhythm A) : still (enroll ζ ∘ A):= by
  intro s x; obtain ⟨P,h,hp⟩:= H s x; refine ⟨P,fun i=>⟨?_,?_,?_⟩⟩
  · exact (congr_arg (fun j:Neat n=> j.val.2) (h i)).trans (congr_arg Prod.snd (sent_one ..))
  · exact (congr_arg (fun j:Neat n=> j.val.1) (h i)).trans (congr_arg Prod.fst (sent_one ..))
  intro U; dsimp only [Function.comp_apply,enroll,Lifted.amount]; rw [hp]

variable (W : κ→ Wickless G n τ)

def Garden := ∀ s : Signed,∀ x : Site n, ∃ U : Equiv.Perm κ,∀ i, (W (U i)).extent=swath s x (W i).extent ∧ ∀ v,(W (U i)).value v=(W i).value (pull s x v)

lemma growing (H : Garden W) : Trend (fun i=> (W i).credit ζ):= by
  intro s x; obtain ⟨m,h⟩:=H s x; exact ⟨m,fun i=>⟨(h i).1,fun v=> by rw [vacant,vacant,(h i).2]⟩⟩

-- occurrence pure already, carries an actual real coefficient
structure Virgin {ζ : V→Site n} (p : Lifted G ζ t) : Prop where
  mode : p.fires=quiet V
  real U : p.value U=((p.value U).re:ℂ)
lemma Nreal_inj : Function.Injective (fun u : ℝ => (Nreal u : veil V)) := by
  intro x y h; change S11 (V:=V) _=S11 _ at h; rw [singles,singles] at h
  have ht := congr_arg (fun u:veil V=>u.part (quiet V)) h; simp at ht; exact ht

def restore {ζ : V→Site n} {p : Lifted G ζ t} (_ : Virgin p) : Burst G n t where
  city := ⟨(p.extent,p.inventory),p.needed,p.records⟩
  value U:= (p.value U).re
  meas:= Complex.continuous_re.measurable.comp p.meas
  inv i U:= congr_arg Complex.re (p.inv i U)
  uses U V a b:= congr_arg Complex.re (p.only U V a b)
  flag U he:= p.flag U (fun h=>he (by rw [h];rfl))
lemma adult {ζ : V→Site n} {p : Lifted G ζ t} (h : Virgin p) (U) : p.amount U=Nreal ((restore h).value U) := by
  change Poly.send _ _= S11 _; rw [singles,h.mode]; exact congr_arg _ (h.real U)
lemma rhythm_here {ζ : V→Site n} {K : κ→Lifted G ζ t} (h : still K) (H : ∀ i, Virgin (K i)) : Rhythm (fun i=> restore (H i)) := by
  intro s x; obtain ⟨m,hp⟩:=h s x; refine ⟨m,fun i=>?_,fun U i=> ?_⟩
  · refine Subtype.ext ?_; rw [sent_one]; exact congr_arg₂ Prod.mk (hp i).extent (hp i).inventory
  apply Nreal_inj (V:=V); dsimp only; rw [← adult,← adult]; exact (hp i).fuel U

lemma peas (j : Domino (enroll ζ ∘ A) (fun i=> (W i).credit ζ) X) :
    Virgin (teat _ _ _ j) := by
  let B:= enroll ζ ∘ A; let C:= fun i=> (W i).credit ζ; let P:= teat B C X
  change Virgin (P j)
  have hh i: chosen B C i=quiet V := by rcases i with (i|i)|i <;> rfl
  have hz : (P j).fires=quiet V:= by
    change scene (alarmCount B C j.val)=_; apply Subtype.ext; ext x; simp [alarmCount,scene,hh,quiet,Census.quiet]
  have hx (i U) : ∃ z : ℝ, fuel B C X i U=Nreal z := by
    rcases i with (i|i)|i
    · exact ⟨(A i).value U,(singles _).symm⟩
    · exact ⟨_, vacant ζ _ U⟩
    exact ⟨_,rfl⟩
  refine ⟨hz,fun U=> ?_⟩; choose m hm using hx
  have h : ∃ z : ℝ, (P j).amount U=Nreal z:= by
    unfold P; rw [teat_pay]; split
    · unfold quake; simp_rw [hm]; exact ⟨_,(map_prod ..).symm⟩
    exact ⟨0,(map_zero ..).symm⟩
  obtain ⟨i,h⟩:= h; change Poly.send _ _=S11 _ at h; rw [singles,hz] at h
  have hf := congr_arg (fun u:veil V=>u.part (quiet V)) h
  change (Poly.send _ _).part _= _ at hf; rw [Poly.part_send,if_pos rfl] at hf; rw [Poly.part_send,if_pos rfl] at hf; rw [hf]; simp

lemma order {ζ : V→Site n} (K : κ→Lifted G ζ τ) (h : ∀ i, Virgin (K i)) (x : Finset κ) (U) :
    Lifted.pack K x U = Nreal (placed (fun i=>restore (h i)) x U):= by
  rw [Lifted.pack, placed,peeled]; split_ifs
  · rw [map_prod]; apply prod_congr rfl; intro i _; exact adult (h i) U
  · contradiction
  · contradiction
  rw [map_zero]
lemma budget_return {ζ : V→Site n} {p : BudgetPoint} {K : κ→Lifted G ζ p.threshold} (h : ∀ i, Virgin (K i))
    {r : V→ℝ} {e w} (H : prepared (q:=p) K r e w) : SumHit (p:=p) (fun i=>restore (h i)) e w:= by
  obtain ⟨m,hm,hv⟩:=H
  refine ⟨m,fun i=>⟨(hm i).1,fun U=>?_⟩,hv⟩
  have ht:=(hm i).2 U; rw [← Poly.solo] at ht; change Poly.price r ((K i).amount _)≤_ at ht; rwa [adult (h i),Nprice] at ht

variable {p q : BudgetPoint}

def Verse (W : κ→ Wickless G n τ) (q : BudgetPoint) (e w : ℝ) := ∃ Z : κ→ℝ,(∀ i,0 ≤ Z i ∧ ∀ U,|(W i).value U| ≤ Z i) ∧ Incur (fun i=> (W i).extent) q.B Z e w
lemma salary {W : κ→Wickless G n q.threshold} {a b : ℝ} (H : Verse W q a b) (r : V→ℝ) :
    taxable (q:=q) (fun i=> (W i).credit ζ) r a b := by
  obtain ⟨u,hu,hQ⟩:=H
  refine ⟨u,fun i=> ⟨(hu i).1, fun U=> ?_⟩,hQ⟩
  change Poly.toll r (quiet V)*‖(↑((W i).value U):ℂ)‖ ≤ _; simp only [Poly.toll,quiet,Census.quiet,prod_empty,one_mul,Complex.norm_real]; exact (hu i).2 U

variable [Fintype ι] [Fintype κ]

theorem regal {A : ι → Burst G n t} {W : κ→Wickless G n q.threshold} {X : Siren G n q.threshold}
    {r : V→ℝ} {u p w e d a : ℝ} (h : Rhythm A) (ht : Garden W) (hx : Peace X) (he : q.threshold≤ t) (hr : ∀ i,0<r i)
    (hp : Verse W q (a+1) p) (hh : Burden (enroll ζ ∘ A) q r (a+1) w) (hg : fertile (q:=q) X u (a+1) e)
    (hF : (↑((q.B+q.B+1)^4:ℕ):ℝ)*d≤1) (hd : p+w+e≤d) (ha : 0≤a) (hy : 0≤u) (hz : 0≤d) : ∃ R : Neat n→Burst G n q.threshold,
      (∀ i,(R i).city=i) ∧ Rhythm R ∧ SumHit (p:=q) R a (Real.exp (-u)*(Real.exp d-1)) ∧ (∀ x U,column (teat (enroll ζ ∘ A) (fun i=> (W i).credit ζ) X) x U = (↑((R x).value U):ℂ)) ∧ ∀ U,
      (∑ i,placed R i U)=(∑ i,placed A i U)*(∏ i,( (W i).value U + 1))*(∏ i∈flags q.threshold U,X.value i U) := by
  let B := enroll ζ ∘ A
  let C := fun i=> (W i).credit ζ
  let D:=teat B C X
  have hf (i) : Virgin (D i) := peas ζ A X W i
  let Y := fun i=> restore (hf i)
  have hm : Rhythm Y := rhythm_here (resumes B C X (sturdy ζ A h) (growing ζ W ht) hx) hf
  have Hh := budget_return hf (rarity B C X hr (salary ζ hp r) hh hg hF hd ha hy hz)
  obtain ⟨R,hr,hH,hW,hBg,hB⟩:=accommodate Y hm Hh ha (fun _=>(hasSum_fintype _).summable)
  refine ⟨R,hr,hH,hW,fun i U=>?_,fun U=>?_⟩
  · rw [hBg,tsum_fintype,Complex.ofReal_sum]; unfold column
    apply sum_congr rfl; intro j _
    let y := (Y j).city
    have h: ((D j).extent,(D j).inventory)=y.val:=rfl
    have hh : (teat (enroll ζ ∘ A) (fun i=> (W i).credit ζ) X j).fires=quiet V:= (hf j).mode
    simp_rw [hh]; rw [h]; simp only [true_and]; change (if y.val=i.val then _ else _)=(↑(if y=i then (Y j).value U else (0:ℝ)):ℂ)
    by_cases he:y=i
    · rw [if_pos (congr_arg _ he),if_pos he]; exact (hf j).real U
    rw [if_neg (fun he' => he (Subtype.ext he')),if_neg he, Complex.ofReal_zero]
  rw [hB,tsum_fintype]; apply Nreal_inj (V:=V); dsimp only; rw [map_sum,map_mul,map_mul,map_sum,map_prod,map_prod]
  calc
    _ = ∑ i,Lifted.pack D i U:= by simp_rw [order D hf]; rfl
    _ = _ := (charade B C X U he).symm.trans <| by
      simp_rw [B,enrolment, map_add, map_one]; dsimp only [C,D]; simp only [vacant]
end YM.Next.Rank.Alarm
